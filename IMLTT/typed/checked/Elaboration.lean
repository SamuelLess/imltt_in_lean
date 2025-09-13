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

partial def elabATm (cx : ElabCtx): TSyntax `atm → TermElabM Q((n : Nat) × ATm n)
  | `(atm| $id:ident) => do
    let id := id.getId
    if let some ⟨n, i⟩ := cx.getFinIdx? id then
      return q(⟨$n, ATm.var $i⟩)
    else
      throwError "Unexpected identifier {id}, not in context"
  | `(atm| ($t:atm)) => elabATm cx t
  -- types
  | `(atm| 𝟘) => do
    let n : Nat := cx.length
    return q(⟨$n, ATm.empty⟩)
  | `(atm| 𝟙) => do
    let n : Nat := cx.length
    return q(⟨$n, .unit⟩)
  | `(atm| 𝒩) => do
    let n : Nat := cx.length
    return q(⟨$n, .nat⟩)
  | `(atm| 𝒰) => do
    let n : Nat := cx.length
    return q(⟨$n, .univ⟩)
  | `(atm| Π ($id:ident : $A:atm; $B:atm)) => do
    let ~q(⟨$n, $AE⟩) ← elabATm cx A
      | throwErrorAt A "Expected a type"
    let id' := id.getId
    let ~q(⟨$n', $BE⟩) ← elabATm (cx.extend id') B
      | throwErrorAt B "Expected a type"
    if ← isDefEq q($n') q($n+1) then
      let piE : Q(ATm $n) := mkApp3 (mkConst ``ATm.pi) n AE BE
      return q(⟨$n, $piE⟩)
    else
      throwErrorAt B m!"Context length mismatch: expected {n'}+1, got {n}"
  --terms
  | `(atm| ⋆) => do
    let n : Nat := cx.length
    return q(⟨$n, .tt⟩)
  | `(atm| 𝓏) => do
    let n : Nat := cx.length
    return q(⟨$n, .zeroNat⟩)
  | `(atm| 𝓈($t:atm)) => do
    let ~q(⟨$n, $t⟩) ← elabATm cx t
      | throwErrorAt t "Expected a term of type Nat"
    return q(⟨$n, .succNat $t⟩)
  | `(atm| λ ($id:ident : $A:atm). $b:atm) => do
    let ~q(⟨$n, $AE⟩) ← elabATm cx A
      | throwErrorAt A "Expected a type"
    let id' := id.getId
    let ~q(⟨$n', $bE⟩) ← elabATm (cx.extend id') b
      | throwErrorAt b "Expected a term"
    if ← isDefEq q($n') q($n+1) then -- this check is for a better error
      let lamE : Q(ATm $n) := mkApp3 (mkConst ``ATm.lam) n AE bE
      return q(⟨$n, $lamE⟩)
    else
      throwErrorAt b m!"Context length mismatch: expected {n'}+1, got {n}"
  | _ => throwUnsupportedSyntax

elab "[tt|" t:atm "]" : term => elabATm [] t

example : ATm 0 := [tt| 𝟙].2
#check [tt| λ (x : 𝟙). ⋆]
#check [tt| Π (x : 𝒰; x)]

partial def elabACtx (cx : ElabCtx) : TSyntax `actx → TermElabM (ElabCtx × Q((n : Nat) × ACtx n))
  | `(actx| ε) => do
    return ⟨[], q(⟨0, ACtx.empty⟩)⟩
  | `(actx| $Γ:actx ⬝ ($id:ident : $A:atm)) => do
    let id' := id.getId
    let ⟨cx', ~q(⟨$n, $ΓE⟩)⟩ ← elabACtx cx Γ | throwErrorAt Γ "Expected a context"
    let ~q(⟨$n', $AE⟩) ← elabATm cx' A | throwErrorAt A "Expected a type"
    if ← isDefEq q($n') q($n) then
      let name := mkApp (mkConst ``String.toName) (mkStrLit id'.toString)
      let extE : Q(ACtx ($n+1)) :=
        mkApp4 (mkConst ``ACtx.extend) n name ΓE AE
      return ⟨cx'.extend id', q(⟨$n+1, $extE⟩)⟩
    else
      throwErrorAt A m!"Term missmatch: expected context length {n'} got {n}"
  | _ => throwUnsupportedSyntax


elab "[tcx|" Γ:actx "]" : term => elabACtx [] Γ >>= (return ·.2)

#check [tcx| ε]
#check ([tcx| ε ⬝ (x : 𝟙)].1 : Nat)
#check [tcx| ε ⬝ (x : 𝟙) ⬝ (y : 𝒰) ⬝ (z : y)]

structure TTm (n : Nat) where
  Γ : Ctx n
  t : Tm n
  T : Tm n
  hasType : Γ ⊢ t ∶ T

partial def elabTTm (stxcx : TSyntax `actx) (stxt stxT : TSyntax `atm) : TermElabM Q((n : Nat) × TTm n) := do
  let ⟨cx, acxq⟩ ← elabACtx [] stxcx
  let ~q(⟨$n, $acx'⟩) := acxq
    | throwErrorAt stxcx "Expected a context"
  let ~q(⟨$nt, $t⟩) ← elabATm cx stxt
    | throwErrorAt stxt "Expected a term"
  let ~q(⟨$nT, $T⟩) ← elabATm cx stxT
    | throwErrorAt stxt "Expected a term"
  let tn : Q(Tm $n) := mkApp (mkConst ``ATm.toTm) t
  let Tn : Q(Tm $n) := mkApp (mkConst ``ATm.toTm) T
  let proof := q(has_type $n ($acx').toCtx $tn $Tn)
  let ttm? : Q(Except _ _) ← whnf proof
  throwError "Not implemented"
  --let ttm? := q(infer [] $t)
  /-
  let ttm? : Q(Option (Σ' T, [] ⊢ $t ∶ T)) ← whnf ttm?
  match ttm? with
  | ~q(Option.some $p) =>
    let p : Q(Σ' T, [] ⊢ $t ∶ T) ← whnf p
    match p with
    | ~q(⟨$T, $p'⟩) =>
      return q({ Γ := [], t := $t, T := $T, hasType := $p'})
  | _ => throwError "type-incorrect!"
  -/
