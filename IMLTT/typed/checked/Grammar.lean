import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.checked.TypeChecker

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command

-- syntax for inductive Tm type
declare_syntax_cat tm (behavior := both)

-- 'types'
syntax "𝟙" : tm
syntax "𝟘" : tm
syntax "Π " tm ", " tm : tm
-- 'terms'
--syntax ident : tm
syntax "⋆" : tm
syntax "λ " ident " : " tm ". " tm : tm
syntax tm tm : tm
syntax tm " → " tm : tm -- Pi type
syntax "(" tm ")" : tm

#check_failure `(tm|𝟙 → 𝟙)
#check_failure `(tm|Π 𝟙, 𝟙)

partial def parseTm : TSyntax `tm → TermElabM (Tm n)
  | `(tm| ($t:tm)) => parseTm t
  | `(tm| ⋆) => pure Tm.tt
  | `(tm| 𝟙) => pure Tm.unit
  | `(tm| 𝟘) => pure Tm.empty
  | `(tm| Π $A:tm, $B:tm) => do
    let A ← parseTm A
    let B ← parseTm B
    pure <| Tm.pi A B
  -- identifier are a future me problem, should be replaced in B n stuff
  | `(tm| λ $_:ident : $A:tm. $B:tm) => do
    let A ← parseTm A
    let B ← parseTm B
    pure <| Tm.lam A B
  | `(tm| $A:tm $B:tm) => do
    let A ← parseTm A
    let B ← parseTm B
    pure <| Tm.app A B
  | _ => throwUnsupportedSyntax


-- syntax for inductive Ctx type
declare_syntax_cat ctxx (behavior := both)
syntax "ε" : ctxx
syntax ctxx " ⬝ " ident " : " tm : ctxx

#check_failure `(ctxx| ε ⬝ x : 𝟙)

def parseCtx : (stx : TSyntax `ctxx) → Option ((n: Nat) × Ctx n)
  | `(ctxx|ε) => some ⟨0, Ctx.empty⟩
  --| `(ctxx|$cx:ctxx ⬝ $id:ident : $ty:tm) => (parseCtx cx).extend (parseTm ty)
  | _ => none


elab "#judge " t:tm : command => do
  let term ← liftTermElabM (parseTm t)
  let ctxx := Ctx.empty
  let res : Option (PLift (ctxx ⊢ term type)) := is_type fuel 0 ctxx term
  match res with
  | some _proof => logInfo s!"TYPE: ε ⊢ {t} type"
  | none => logInfo s!"NOT A TYPE in ε"

#judge 𝟙
#judge (Π 𝟙, 𝟙)
#judge ((λ x:𝟙. 𝟙) 𝟙)

elab "#check_ty " t:tm " ∶ " T:tm : command => do
  let term ← liftTermElabM <| parseTm t
  let ty ← liftTermElabM <| parseTm T
  let ctxx := Ctx.empty -- to be included in syntax
  let res : Option (PLift (ctxx ⊢ term ∶ ty)) := has_type fuel ctxx term ty
  match res with
  | some _proof => logInfo s!"Checked: ε ⊢ {t} ∶ {T}"
  | none => logInfo s!"Type could not be inferred in ε"


#check_ty (⋆) ∶ (𝟙)

#check_ty (λ x:𝟙. 𝟙) ∶ Π 𝟙 , 𝟙

example : ε ⊢ ((λ𝟙; v(0))◃𝟙) type := by sorry
example : ε ⊢ ((λ𝟙; 𝟙)◃⋆) ∶ 𝒰 := by
  have hεctx : ε ctx := IsCtx.empty
  have hLamPi : ε ⊢ (λ𝟙; 𝟙) ∶ Π𝟙;𝒰 := by
    apply HasType.pi_intro
    apply HasType.univ_unit
    exact IsCtx.extend hεctx (IsType.unit_form hεctx)
  apply HasType.ty_conv
  · apply HasType.pi_elim
    · exact hLamPi
    · exact star_unit
  · exact IsEqualType.univ_form_eq hεctx


-- syntax for judgments
declare_syntax_cat judgment (behavior := both)
syntax ctxx " ⊢ " tm " type" : judgment
syntax ctxx " ⊢ " tm " ∶ " tm : judgment

#check_failure `(judgment| ε ⊢ 𝟙 type)

syntax (name := judge_term) "%% " term " ⊢ " tm " type" : term

@[term_elab judge_term]
def judgeElab : TermElab := fun stx _ => do
  /-let `((%% $cx:term ⊢ $t:tm type)) := stx
    | throwUnsupportedSyntax
  let ctx := parseCtx ctxx
  let term := denoteTm t
  match is_type fuel cx term with
  | some proof => logInfo s!"'{ctxx} ⊢ {term} type' is valid by proof: {proof}"
  | none => logInfo s!"'{ctxx} ⊢ {term} type' is not valid"-/
  sorry

syntax (name := notType) "(" term  " !: " term ")" : term

@[term_elab notType]
def elabNotType : TermElab := fun stx _ => do
  let `(($tm:term !: $ty:term)) := stx
    | throwUnsupportedSyntax
  let unexpected ← elabType ty
  let e ← elabTerm tm none
  let eTy ← Meta.inferType e
  if (← Meta.isDefEq eTy unexpected) then
    throwErrorAt tm m!"Got unwanted type {eTy}"
  else pure e
