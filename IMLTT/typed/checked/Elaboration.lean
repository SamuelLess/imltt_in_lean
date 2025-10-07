import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.checked.TypeChecker
import IMLTT.typed.AnnotatedSyntax
import Qq

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command Qq Tactic

namespace ElabTm

example (n : Q(Nat)) (h : Q($n = 3)): Q(Vector Nat ($n)) :=
  q(Vector.mk #[1,2,3] (Eq.symm $h))

def ElabCtx := List Name

namespace ElabCtx

protected def empty : ElabCtx := []

def extend (Γ : ElabCtx) (name : Name) : ElabCtx :=
  name :: Γ

#check List.findFinIdx?

def getFinIdx? (cx : ElabCtx) (name : Name) : Option ((n : Nat) × (Fin n)) :=
  cx.findFinIdx? (·==name) |>.map (⟨cx.length, ·⟩)

end ElabCtx

partial def elabATm (cx : ElabCtx): TSyntax `atm → TermElabM ((n : Nat) × ATm n)
  | `(atm| $id:ident) => do
    let id := id.getId
    if let some ⟨n, i⟩ := cx.getFinIdx? id then
      return ⟨n, ATm.var i⟩
    else
      throwError "Unexpected identifier {id}, not in context"
  | `(atm| ($t:atm)) => elabATm cx t
  -- types
  | `(atm| 𝟘) => do
    let n : Nat := cx.length
    return ⟨n, .empty⟩
  | `(atm| 𝟙) => do
    let n : Nat := cx.length
    return ⟨n, .unit⟩
  | `(atm| 𝒩) => do
    let n : Nat := cx.length
    return ⟨n, .nat⟩
  | `(atm| 𝒰) => do
    let n : Nat := cx.length
    return ⟨n, .univ⟩
  | `(atm| Π ($id:ident : $A:atm; $B:atm)) => do
    let ⟨n, AE⟩ ← elabATm cx A
    let id' := id.getId
    let ⟨n', BE⟩ ← elabATm (cx.extend id') B
    --if ← isDefEq q($n') q($n+1) then
    if h : n+1 = n' then
      let bbE : (ATm (n+1)) := by
        rw [h]
        exact BE
      let piE : (ATm n) := ATm.pi AE bbE
      return ⟨n, piE⟩
    else
      throwErrorAt B m!"Context length mismatch: expected {n'}+1, got {n}"
  --terms
  | `(atm| ⋆) => do
    let n : Nat := cx.length
    return ⟨n, .tt⟩
  | `(atm| 𝓏) => do
    let n : Nat := cx.length
    return ⟨n, .zeroNat⟩
  | `(atm| 𝓈($t:atm)) => do
    let ⟨n, t⟩ ← elabATm cx t
    return ⟨n, .succNat t⟩
  | `(atm| λ ($id:ident : $A:atm). $b:atm) => do
    let ⟨n, AE⟩ ← elabATm cx A
    let id' := id.getId
    let ⟨n', bE⟩ ← elabATm (cx.extend id') b
    if h : n+1 = n' then
      let bbE : (ATm (n+1)) := h ▸ bE
      let lamE : (ATm n) := ATm.lam AE bbE
      return ⟨n, lamE⟩
    else
      throwErrorAt b m!"Context length mismatch: expected {n'}+1, got {n}"
  | _ => throwUnsupportedSyntax

elab "[ttm|" t:atm "]" : term => do
  let ⟨_, atm⟩ ← elabATm [] t
  return Lean.toExpr atm

example : ATm 0 := [ttm| 𝟙]
#check [ttm| λ (x : 𝟙). ⋆]
#check [ttm| Π (x : 𝒰; x)]

partial def elabACtx (cx : ElabCtx) : TSyntax `actx → TermElabM (ElabCtx × ((n : Nat) × ACtx n))
  | `(actx| ε) => do
    return ⟨[], (⟨0, ACtx.empty⟩)⟩
  | `(actx| $Γ:actx ⬝ ($id:ident : $A:atm)) => do
    let id' := id.getId
    let ⟨cx', ⟨n, ΓE⟩⟩ ← elabACtx cx Γ
    let ⟨n', AE⟩ ← elabATm cx' A
    if h : n = n' then
      let AE' : (ATm n) := h ▸ AE
      let extE : (ACtx (n+1)) :=
        ACtx.extend id' ΓE AE'
      return ⟨cx'.extend id', ⟨n+1, extE⟩⟩
    else
      throwErrorAt A m!"Term missmatch: expected context length {n'} got {n}"
  | _ => throwUnsupportedSyntax


elab "[tcx|" Γ:actx "]" : term => do
  let ⟨_, ⟨_, actx⟩⟩ ← elabACtx [] Γ
  return Lean.toExpr actx

#check [tcx| ε]
#check [tcx| ε ⬝ (x : 𝟙) ⬝ (y : 𝒰) ⬝ (z : y)]

structure TTm (n : Nat) where
  Γ : Ctx n
  t : Tm n
  T : Tm n
  hasType : Γ ⊢ t ∶ T

partial def elabTTm (stxcx : TSyntax `actx) (stxt stxT : TSyntax `atm) : TermElabM Q((n : Nat) × TTm n) := do
  let ⟨cx, ⟨n, actx⟩⟩ ← elabACtx [] stxcx
  let ⟨nt, atm⟩ ← elabATm cx stxt
  let ⟨nT, aTm⟩ ← elabATm cx stxT
  if h : n = nt ∧ n = nT then
    let t : Tm n := h.left ▸ atm.toTm
    let T : Tm n := h.right ▸ aTm.toTm
    match has_type 30 actx.toCtx t T with
    | Except.ok _ =>
      let ctxE : Q(Ctx $n) := Lean.toExpr (actx.toCtx)
      let tE : Q(Tm $n) := Lean.toExpr t
      let TE : Q(Tm $n) := Lean.toExpr T
      match ← whnf q(has_type 30 $ctxE $tE $TE) with
      | mkApp _ pr =>
        let ttm := mkApp5 (mkConst ``TTm.mk) (mkNatLit n) ctxE tE TE (← mkAppM ``PLift.down #[pr])
        return ttm
      | _ => throwError "Could not find proof again o.O"
    | Except.error msg =>
      throwErrorAt stxt "Type error: { msg }"
  else throwErrorAt stxt m!"Context length mismatch: expected {n}, got {nt} and {nT}"

elab "[tt|" cx:actx "⊢" t:atm ":" T:atm "]" : term => elabTTm cx t T

def test1 := [tt| ε ⊢ ⋆ : 𝟙]
/-- error: Type error: is_eq_type: out of fuel 𝒰 ≡ 𝟙 -/
#guard_msgs in
def test2 := [tt| ε ⊢ ⋆ : 𝒰]
def test3 := [tt| ε ⊢ 𝓈(𝓏) : 𝒩]

syntax "ttheorem " ident " : " actx "⊢" atm ":" atm : command
macro_rules
  | `(ttheorem $id:ident : $cx:actx ⊢ $t:atm : $T:atm) => do
    let ttm_name := Name.str id.getId "_TTm"
    let ttm_id := mkIdent ttm_name
    `(def $ttm_id:ident := [tt| $cx ⊢ $t : $T]
      theorem $id : ($ttm_id).Γ ⊢ ($ttm_id).t ∶ ($ttm_id).T := ($ttm_id).hasType)

ttheorem test8 : ε ⊢ ⋆ : 𝟙
#check test8
