import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.checked.TypeChecker
import Qq

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command Qq

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
syntax "𝓈(" tm ")" : tm
syntax "λ " "(" ident " : " tm  ")" ". " tm " :: " tm : tm
syntax "λ " "(" ident " : " tm  ")" ". " tm : tm
syntax "(" tm "&" tm ")" "::" tm : tm
syntax tm tm : tm
syntax "ind𝟙" tm tm tm : tm
syntax "(" tm ")" : tm

#check_failure `(tm|𝟙 → 𝟙)
#check_failure `(tm|λ(x : 𝟙). x :: 𝟙)
#check_failure `(tm|Π(x : 𝟙;𝟙))
#check_failure `(tm|Σ(x : 𝒰;x))


inductive ATm : Nat → Type where
  -- 'types'
  | unit : ATm n
  | empty : ATm n
  | pi : Name → ATm n → ATm (n + 1) → ATm n
  | sigma : Name → ATm n → ATm (n + 1) → ATm n
  | nat : ATm n
  | iden : ATm n → ATm n → ATm n → ATm n
  | univ : ATm n
  -- 'terms'
  | var : Name → Fin n → ATm n -- added name and meaning of Fin n becomes stack height
  | tt : ATm n
  | indUnit : ATm (n + 1) → ATm n → ATm n → ATm n
  | indEmpty : ATm (n + 1) → ATm n → ATm n
  -- λx:A. b B where b⌈x⌉ : B⌈x⌉
  | lam : Name → ATm n → ATm (n + 1) → ATm (n + 1) → ATm n -- added λ type annotation
  | app : ATm n → ATm n → ATm n
  -- a & b : Σ (dependent)
  | pairSigma : ATm n → ATm n → ATm n → ATm n -- add Σ type annotation
  | indSigma: ATm n → ATm (n + 1) → ATm (n + 1) → ATm (n + 2) → ATm n → ATm n
  | zeroNat : ATm n
  | succNat : ATm n → ATm n
  | indNat : ATm (n + 1) → ATm n → ATm (n + 2) → ATm n → ATm n
  | refl : ATm n → ATm n → ATm n
  | j : ATm n → ATm (n + 3) → ATm (n + 1) → ATm n → ATm n → ATm n → ATm n
  deriving Repr, Nonempty

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
  | extend : ACtx n → (id : Name) → ATm n → ACtx (n + 1)
  deriving Repr

instance : Inhabited ((n : Nat) × ACtx n) := ⟨⟨0, ACtx.empty⟩⟩

def ACtx.toList : ACtx n → List ((n : Nat) × Name × ATm n)
  | .empty => []
  | @ACtx.extend n cx id ty => ⟨n, id, ty⟩ :: cx.toList

theorem ACtx.length {n} (cx : ACtx n) : cx.toList.length = n := by
  induction cx with
  | empty => simp only [toList, List.length_nil]
  | extend cx' id ty ih => simp only [toList, List.length_cons, ih]

notation cx " a⬝ " "(" id " : " ty ")" => ACtx.extend cx id ty

def ACtx.toCtx {n} : ACtx n → Ctx n
  | .empty => Ctx.empty
  | .extend cx _ ty => Ctx.extend (ACtx.toCtx cx) (ty.toTm)

partial def elabATm (cx : ACtx n) : TSyntax `tm → TermElabM (ATm n)
  | `(tm| ($t:tm)) => elabATm cx t
  -- types
  | `(tm| 𝟘) => pure .empty
  | `(tm| 𝟙) => pure .unit
  | `(tm| 𝒩) => pure .nat
  | `(tm| 𝒰) => pure .univ
  | `(tm| Π ($id:ident : $A:tm; $B:tm)) => do
    let A  ← elabATm cx A
    let B ← elabATm (cx a⬝ (id.getId : A)) B
    pure <| .pi id.getId A B
  | `(tm| Σ ($id:ident : $A:tm; $B:tm)) => do
    let A  ← elabATm cx A
    let B ← elabATm (cx a⬝ (id.getId : A)) B
    pure <| .sigma id.getId A B
  -- terms
  | `(tm| ⋆) => pure .tt
  | `(tm| 𝓏) => pure .zeroNat
  | `(tm| 𝓈($t:tm)) => do
    let t ← elabATm cx t
    pure <| .succNat t
  | `(tm| λ ($id:ident : $A:tm). $b:tm :: $B:tm) => do
    let A  ← elabATm cx A
    let b ← elabATm (cx a⬝ (id.getId : A)) b
    let B ← elabATm (cx a⬝ (id.getId : A)) B
    pure <| .lam id.getId A b B
  | `(tm| λ ($id:ident : $A:tm). $b:tm) => do
    let A  ← elabATm cx A
    let b ← elabATm (cx a⬝ (id.getId : A)) b
    --let B ← parseATm (cx a⬝ (id : A)) B
    pure <| .lam id.getId A b .empty
  | `(tm|  ($a:tm&$b:tm) :: $S:tm) => do
    let S  ← elabATm cx S
    let a  ← elabATm cx a
    let b  ← elabATm cx b
    pure <| .pairSigma a b S
  | `(tm| $f:tm $a:tm) => do
    let f ← elabATm cx f
    let a ← elabATm cx a
    pure <| .app f a
  | `(tm| $id:ident) => do
    match n with
    | 0 => throwErrorAt id m!"No variables in context"
    | n' + 1 => do
      let cxlist : List Name := cx.toList.map (·.2.1)
      let (some ⟨i, hi⟩) := cxlist.findFinIdx? (· == id.getId)
        | throwErrorAt id m!"Variable {id} not in context {cxlist}"
      have : cxlist.length = n' + 1 := by
        simp only [cxlist, List.length_map]
        exact ACtx.length cx
      pure <| .var id.getId ⟨i, Nat.lt_of_lt_of_eq hi this⟩
  | _ => throwUnsupportedSyntax

-- syntax for inductive ACtx type
declare_syntax_cat ctxx (behavior := both)
syntax "ε" : ctxx
syntax ctxx " ⬝ " " ( " ident " : " tm  " ) " : ctxx

#check_failure `(ctxx| ε ⬝ (x : 𝟙))
#check_failure `(ctxx| ε ⬝ (T : 𝒰) ⬝ (t : T))

#check (ε ⬝ 𝒩 : Ctx 1)

partial def elabACtx : (stx : TSyntax `ctxx) → TermElabM ((n : Nat) × ACtx n)
  | `(ctxx|ε) => pure ⟨0, .empty⟩
  | `(ctxx|$cx:ctxx ⬝ ($id:ident : $ty:tm)) => do
    let ⟨n', cx'⟩ ← elabACtx cx
    let nty ← elabATm cx' ty
    let newCtx := ACtx.extend cx' id.getId nty
    pure ⟨n' + 1, newCtx⟩
  | _ => throwUnsupportedSyntax

elab "#imltt " cx:ctxx "⊢" t:tm : command => do
  let ⟨_, acontext⟩ ← liftTermElabM (elabACtx cx)
  let aterm ← liftTermElabM (elabATm acontext t)
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
  let ⟨_, acontext⟩ ← liftTermElabM (elabACtx cx)
  let aterm ← liftTermElabM (elabATm acontext t)
  let atype ← liftTermElabM (elabATm acontext T)
  let ctxlist := acontext.toList.map (·.2.1)|>.reverse
  logInfo s!"Context: {ctxlist}, term: {aterm.toTm}"
  let res := has_type fuel (ACtx.toCtx acontext) aterm.toTm atype.toTm
  match res with
  | .ok _ => logInfo s!"Found proof that: {ctxlist} ⊢ {aterm.toTm} : {atype.toTm}."
  | .error err  => logInfo s!"Type error: {err}"

#imltt ε ⬝ (A : 𝒰) ⬝ (IdA : Π(a : A; A)) ⬝ (a : A) ⊢ (λ(x : A). (IdA x) :: A) a : A
#imltt ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⊢ λ(x : A). (x&x) :: Σ(a : A;A) :: Σ(a : A; A) : Σ(a : A; A)

#imltt ε ⊢ ((λ(x : 𝒩). x :: 𝒩) 𝓏) : 𝒩

#imltt ε ⬝ (A : 𝒰) ⬝ (IdA : Π(a : A; A)) ⬝ (a : A) ⊢ (IdA a) : A

#imltt ε ⬝ (x : 𝒩) ⬝ (u : 𝟙) ⊢ (((λ(i:𝒩). (𝓈(i)&(((λ(T: 𝒰). (λ(t : T). t)) 𝒩) i)) :: (Σ(a:𝒩;𝒩))))) x : Σ(a:𝒩;𝒩)

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
    · aesop
  · exact IsEqualType.univ_form_eq hεctx

example : ε ⊢ ((λ𝟙; 𝟙)◃⋆) ∶ 𝒰 := by
  exact ((has_type fuel _ _ _).toOption.get (by native_decide)).down

syntax "typecheck" : tactic

macro_rules
| `(tactic| typecheck) => `(tactic| exact ((has_type fuel _ _ _).toOption.get (by native_decide)).down)
macro_rules
| `(tactic| typecheck) => `(tactic| exact ((is_type fuel _ _ _).toOption.get (by native_decide)).down)

theorem my_test : ε ⊢ ((λ𝟙; 𝟙)◃⋆) ∶ 𝒰 := by typecheck

theorem my_test' : ε ⬝ 𝒰 ⊢ 𝒰 type := by typecheck

syntax ">> " ctxx "⊢" tm "∶" tm " <<" : term

elab_rules : term
  | `(>> $cx:ctxx ⊢ $t:tm ∶ $T:tm <<) => do
    let ⟨n, acontext⟩ ← elabACtx cx
    let aterm ← elabATm acontext t
    let atype ← elabATm acontext T
    let cxE := Lean.toExpr (ACtx.toCtx acontext)
    let tmE := Lean.toExpr (aterm.toTm)
    let tyE := Lean.toExpr (atype.toTm)

    return mkApp4 (Expr.const ``HasType []) (Lean.Expr.lit <| .natVal n) cxE tmE tyE
elab_rules : term
  | `(>> $cx:ctxx ⊢ $t:tm ∶ $T:tm <<) => do
    let ⟨n, acontext⟩ ← elabACtx cx
    let aterm ← elabATm acontext t
    let atype ← elabATm acontext T
    let cxE := Lean.toExpr (ACtx.toCtx acontext)
    let tmE := Lean.toExpr (aterm.toTm)
    let tyE := Lean.toExpr (atype.toTm)
    return mkApp4 (Expr.const ``HasType []) (Lean.Expr.lit <| .natVal n) cxE tmE tyE


example : >> ε ⬝ (s : 𝟙) ⊢ (λ(x : 𝟙). x) ∶ Π(s : 𝟙;𝟙) << := by typecheck

--example : >> ε ⬝ (s : 𝟙) ⬝ (A : 𝒰) ⬝ (a : A⌈s⌉₀) ⊢ (λ(x : 𝟙). x) ∶ Π(s : 𝟙;𝟙) << := by typecheck

--Γ ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⊢ (λ(g : ΠB;C);(λ(f : ΠA;B);(λ(x : A); g◃(f◃x))) : ΠA;C
theorem comp :
   >> ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⬝ (g' : Π(b : B;C)) ⬝ (f' : Π(a : A;B)) ⊢
    ((λ(g : Π(b : B;C)) . (λ(f : Π(a : A;B)) . (λ(x : A) . g (f x)))) g') f'∶  (Π(a : A;C)) << := by
  typecheck

/-
--Γ ⊢ ΣA;B type → (Γ ⊢ p ∶ ΣA;B) →  Γ ⊢ A.indSigma B (A⌊↑ₚidₚ⌋) (v(0)⌊↑ₚidₚ⌋) p  ∶ A :=
theorem proj1 :
  >> ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (p : Σ(a : A;B)) ⊢ indΣ A B (A) () << := by
  typecheck
-/

syntax "ttheorem " ident " : " term : command

macro_rules
  | `(ttheorem $id:ident : $rule:term) => `(theorem $id : $rule := by typecheck)

ttheorem id_star_unit : >> ε ⬝ (s : 𝟙) ⊢ ((λ(x : 𝟙). x) s) ∶ 𝟙 <<

/-- info: id_star_unit : ε ⬝ 𝟙 ⊢ (λ𝟙; v(0))◃v(0) ∶ 𝟙 -/
#guard_msgs in
#check id_star_unit
