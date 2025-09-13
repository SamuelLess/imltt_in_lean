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

def getIdx? (cx : ElabCtx) (name : Name) : Option Nat :=
  go 0 cx
where
  go (i : Nat) : ElabCtx → Option Nat
    | [] => none
    | n :: cx =>
      if n == name then
        some i
      else
        go (i + 1) cx

end ElabCtx

abbrev ATmElabM := ReaderT ElabCtx TermElabM

protected def ATmElabM.run (x : ATmElabM α) : TermElabM α :=
  ReaderT.run x .empty

def getCtx : ATmElabM ElabCtx :=
  read

partial def elabATm : TSyntax `atm → ATmElabM Q((n : Nat) × ATm n)
  | `(atm| ($t:atm)) => elabATm t
  -- types
  | `(atm| 𝟘) => do
    let n : Q(Nat) := mkNatLit (← getCtx).length
    return q(⟨$n, .empty⟩)
  | `(atm| 𝟙) => do
    let n : Q(Nat) := mkNatLit (← getCtx).length
    return q(⟨$n, .unit⟩)
  | `(atm| 𝒩) => do
    let n : Q(Nat) := mkNatLit (← getCtx).length
    return q(⟨$n, .nat⟩)
  | `(atm| 𝒰) => do
    let n : Q(Nat) := mkNatLit (← getCtx).length
    return q(⟨$n, .univ⟩)
  --terms
  | `(atm| ⋆) => do
    let n : Q(Nat) := mkNatLit (← getCtx).length
    return q(⟨$n, .tt⟩)
  | `(atm| 𝓏) => do
    let n : Q(Nat) := mkNatLit (← getCtx).length
    return q(⟨$n, .zeroNat⟩)
  | `(atm| 𝓈($t:atm)) => do
    let ~q(⟨$n, $t⟩) ← elabATm t
      | throwErrorAt t "Expected a term of type Nat"
    return q(⟨$n, .succNat $t⟩)
  | `(atm| λ ($id:ident : $A:atm). $b:atm) => do
    let ~q(⟨$n, $AE⟩) ← elabATm A
      | throwErrorAt A "Expected a type"
    let id' := id.getId
    let ~q(⟨$n', $bE⟩) ← withReader (·.extend id') <| elabATm b
      | throwErrorAt b "Expected a term"
    if ← isDefEq q($n') q($n+1) then
      let lamE : Q(ATm $n) := mkApp3 (mkConst ``ATm.lam) n AE bE
      return q(⟨$n, $lamE⟩)
    else
      throwErrorAt b m!"Context length mismatch: expected {n'}+1, got {n}"
  | _ => throwUnsupportedSyntax

elab "[tt|" t:atm "]" : term =>
  (elabATm t |>.run)

example : ATm 0 := [tt| 𝟙 ].2
#check [tt| λ (x : 𝟙). ⋆ ]
