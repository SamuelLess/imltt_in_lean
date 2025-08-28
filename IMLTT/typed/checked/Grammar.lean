import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.checked.TypeChecker

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command

-- syntax for inductive Tm type
declare_syntax_cat tm (behavior := both)

-- 'types'
syntax "𝟘" : tm
syntax "𝟙" : tm
syntax "𝒩" : tm
syntax "𝒰" : tm
syntax tm " → " tm : tm -- nondependent Pi type
syntax "Π" "(" ident ":" tm ";"  tm ")" : tm
syntax "Σ" "(" ident ":" tm ";"  tm ")" : tm
-- 'terms'
syntax ident : tm
syntax "⋆" : tm
syntax "𝓏" : tm
syntax "λ " "(" ident " : " tm  ")" ". " tm " :: " tm : tm
syntax "λ " "(" ident " : " tm  ")" ". " tm : tm
syntax "(" tm "&" tm ")" "::" tm : tm
syntax tm tm : tm
syntax "(" tm ")" : tm

#check_failure `(tm|𝟙 → 𝟙)
#check_failure `(tm|λ(x : 𝟙). x :: 𝟙)
#check_failure `(tm|Π(x : 𝟙;𝟙))
#check_failure `(tm|Σ(x : 𝒰;x))


inductive ATm : Nat → Type where
  -- 'types'
  | unit : ATm n
  | empty : ATm n
  | pi : Syntax.Ident → ATm n → ATm (n + 1) → ATm n
  | sigma : Syntax.Ident → ATm n → ATm (n + 1) → ATm n
  | nat : ATm n
  | iden : ATm n → ATm n → ATm n → ATm n
  | univ : ATm n
  -- 'terms'
  | var : Syntax.Ident → Fin n → ATm n -- added name and meaning of Fin n becomes stack height
  | tt : ATm n
  | indUnit : ATm (n + 1) → ATm n → ATm n → ATm n
  | indEmpty : ATm (n + 1) → ATm n → ATm n
  -- λx:A. b B where b⌈x⌉ : B⌈x⌉
  | lam : Syntax.Ident → ATm n → ATm (n + 1) → ATm (n + 1) → ATm n -- added λ type annotation
  | app : ATm n → ATm n → ATm n
  -- a & b : Σ (dependent)
  | pairSigma : ATm n → ATm n → ATm n → ATm n -- add Σ type annotation
  | indSigma: ATm n → ATm (n + 1) → ATm (n + 1) → ATm (n + 2) → ATm n → ATm n
  | zeroNat : ATm n
  | succNat : ATm n → ATm n
  | indNat : ATm (n + 1) → ATm n → ATm (n + 2) → ATm n → ATm n
  | refl : ATm n → ATm n → ATm n
  | j : ATm n → ATm (n + 3) → ATm (n + 1) → ATm n → ATm n → ATm n → ATm n

example {f : Fin n} : n-f.toNat <= n := by simp

#check (ATm.var _ ⟨0, by omega⟩ : ATm (1))

def ATm.toTm {n} : ATm n → Tm n
  | .unit => Tm.unit
  | .empty => Tm.empty
  | .pi _ A B => Tm.pi (A.toTm) (B.toTm)
  | .sigma _ A B => Tm.sigma (A.toTm) (B.toTm)
  | .nat => Tm.nat
  | .iden A a b => Tm.iden (A.toTm) (a.toTm) (b.toTm)
  | .univ => Tm.univ
  | .var _ i => Tm.var i
  | .tt => Tm.tt
  | .indUnit P z c => Tm.indUnit (P.toTm) (z.toTm) (c.toTm)
  | .indEmpty P c => Tm.indEmpty (P.toTm) (c.toTm)
  | .lam _ A b _ => Tm.lam (A.toTm) (b.toTm)
  | .app f a => Tm.app (f.toTm) (a.toTm)
  | .pairSigma a b _ => Tm.pairSigma (a.toTm) (b.toTm)
  | .indSigma A P cs C p => Tm.indSigma (A.toTm) (P.toTm) (cs.toTm) (C.toTm) (p.toTm)
  | .zeroNat => Tm.zeroNat
  | .succNat n => Tm.succNat (n.toTm)
  | .indNat P z s n => Tm.indNat (P.toTm) (z.toTm) (s.toTm) (n.toTm)
  | .refl A a => Tm.refl (A.toTm) (a.toTm)
  | .j A P a b p r => Tm.j (A.toTm) (P.toTm) (a.toTm) (b.toTm) (p.toTm) (r.toTm)

inductive ACtx : Nat → Type where
  | empty : ACtx 0
  | extend : ACtx n → (id : Syntax.Ident) → ATm n → ACtx (n + 1)

def ACtx.toList : ACtx n → List ((n : Nat) × Syntax.Ident × ATm n)
  | .empty => []
  | @ACtx.extend n cx id ty => ⟨n, id, ty⟩ :: cx.toList

theorem ACtx.length {n} (cx : ACtx n) : cx.toList.length = n := by
  induction cx with
  | empty => simp only [toList, List.length_nil]
  | extend cx' id ty ih => simp only [toList, List.length_cons, ih]

notation cx " ⬝ " "(" id " : " ty ")" => ACtx.extend cx id ty

def ACtx.toCtx {n} : ACtx n → Ctx n
  | .empty => Ctx.empty
  | .extend cx _ ty => Ctx.extend (ACtx.toCtx cx) (ty.toTm)

partial def parseATm (cx : ACtx n) : TSyntax `tm → TermElabM (ATm n)
  | `(tm| ($t:tm)) => parseATm cx t
  -- types
  | `(tm| 𝟘) => pure .empty
  | `(tm| 𝟙) => pure .unit
  | `(tm| 𝓏) => pure .zeroNat
  | `(tm| 𝒰) => pure .univ
  | `(tm| Π ($id:ident : $A:tm; $B:tm)) => do
    let A  ← parseATm cx A
    let B ← parseATm (cx ⬝ (id : A)) B
    pure <| .pi id A B
  | `(tm| Σ ($id:ident : $A:tm; $B:tm)) => do
    let A  ← parseATm cx A
    let B ← parseATm (cx ⬝ (id : A)) B
    pure <| .sigma id A B
  -- terms
  | `(tm| ⋆) => pure .tt
  | `(tm| 𝒩) => pure .nat
  | `(tm| λ ($id:ident : $A:tm). $b:tm :: $B:tm) => do
    let A  ← parseATm cx A
    let b ← parseATm (cx ⬝ (id : A)) b
    let B ← parseATm (cx ⬝ (id : A)) B
    pure <| .lam id A b B
  | `(tm|  ($a:tm&$b:tm) :: $S:tm) => do
    let S  ← parseATm cx S
    let a  ← parseATm cx a
    let b  ← parseATm cx b
    pure <| .pairSigma a b S
  | `(tm| $f:tm $a:tm) => do
    let f ← parseATm cx f
    let a ← parseATm cx a
    pure <| .app f a
  | `(tm| $id:ident) => do
    match n with
    | 0 => throwErrorAt id m!"No variables in context"
    | n' + 1 => do
      let cxlist := cx.toList.map (·.2.1)
      let (some ⟨i, hi⟩) := cxlist.findFinIdx? (· == id)
        | throwErrorAt id m!"Variable {id} not in context {cxlist}"
      have : cxlist.length = n' + 1 := by
        simp only [cxlist, List.length_map]
        exact ACtx.length cx
      pure <| .var id ⟨i, Nat.lt_of_lt_of_eq hi this⟩
  | _ => throwUnsupportedSyntax

-- syntax for inductive ACtx type
declare_syntax_cat ctxx (behavior := both)
syntax "ε" : ctxx
syntax ctxx " ⬝ " " ( " ident " : " tm  " ) " : ctxx

#check_failure `(ctxx| ε ⬝ (x : 𝟙))
#check_failure `(ctxx| ε ⬝ (T : 𝒰) ⬝ (t : T))

#check (ε ⬝ 𝒩 : Ctx 1)

partial def parseACtx : (stx : TSyntax `ctxx) → TermElabM ((n : Nat) × ACtx n)
  | `(ctxx|ε) => pure ⟨0, .empty⟩
  | `(ctxx|$cx:ctxx ⬝ ($id:ident : $ty:tm)) => do
    let ⟨n', cx'⟩ ← parseACtx cx
    let nty ← parseATm cx' ty
    let newCtx := ACtx.extend cx' id nty
    pure ⟨n' + 1, newCtx⟩
  | _ => throwUnsupportedSyntax



elab "#imltt " cx:ctxx "⊢" t:tm : command => do
  let ⟨_, acontext⟩ ← liftTermElabM (parseACtx cx)
  let aterm ← liftTermElabM (parseATm acontext t)
  logInfo s!"Context: {acontext.toList.map (·.2.1)|>.reverse}, term: {aterm.toTm}"
  let res := is_type fuel _ (ACtx.toCtx acontext) aterm.toTm
  match res with
  | .ok _ => logInfo s!"The term is a valid type."
  | .error err  => logInfo s!"Type error: {err}"

#imltt ε ⊢ 𝓏
#imltt ε ⬝ (T : 𝒰) ⬝ (t : 𝒩) ⊢ λ(x : 𝒰).x :: T
#imltt ε ⬝ (a : 𝒰) ⬝ (b : 𝒩) ⬝ (c : 𝒩) ⬝ (d : 𝒩) ⬝ (e : 𝒩) ⊢ c
#imltt ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⊢ A

elab "#imltt " cx:ctxx "⊢" t:tm  " : " T:tm : command => do
  let ⟨_, acontext⟩ ← liftTermElabM (parseACtx cx)
  let aterm ← liftTermElabM (parseATm acontext t)
  let atype ← liftTermElabM (parseATm acontext T)
  let ctxlist := acontext.toList.map (·.2.1)|>.reverse
  logInfo s!"Context: {ctxlist}, term: {aterm.toTm}"
  let res := has_type fuel (ACtx.toCtx acontext) aterm.toTm atype.toTm
  match res with
  | .ok _ => logInfo s!"Found proof that: {ctxlist} ⊢ {aterm.toTm} : {atype.toTm}."
  | .error err  => logInfo s!"Type error: {err}"

#imltt ε ⬝ (A : 𝒰) ⬝ (IdA : Π(a : A; A)) ⬝ (a : A) ⊢ (λ(x : A). (IdA x) :: A) a : A
#imltt ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⊢ λ(x : A). (x&x) :: Σ(a : A;A) :: Σ(a : A; A) : Σ(a : A; A)

#imltt ε ⊢ ((λ(x : 𝒩). x :: 𝒩) 𝓏) : 𝒩


#imltt ε ⊢ ((λ(x : 𝟙). 𝟙 :: 𝒰) ⋆) : 𝒰
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

--Γ ⊢ ΣA;B type → (Γ ⊢ p ∶ ΣA;B) →  Γ ⊢ A.indSigma B (A⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) p  ∶ A :=

#imltt ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (p : Σ(a:A;B)) ⊢ A : 𝒰

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
