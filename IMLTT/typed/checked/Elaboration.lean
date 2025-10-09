import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Elaboration
import IMLTT.typed.checked.TypeChecker

import Qq

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command Qq Tactic

structure TTm (n : Nat) where
  Γ : Ctx n
  t : Tm n
  T : Tm n
  hasType : Γ ⊢ t ∶ T

partial def elabTTm (stxcx : TSyntax `actx) (stxt stxT : TSyntax `atm) :
    TermElabM Q((n : Nat) × TTm n) := do
  let ⟨cx, ⟨n, actx⟩⟩ ← elabACtx [] stxcx
  let ⟨nt, atm⟩ ← elabATm cx stxt
  let ⟨nT, aTm⟩ ← elabATm cx stxT
  if h : n = nt ∧ n = nT then
    let t : ATm n := h.left ▸ atm
    let T : ATm n := h.right ▸ aTm
    match has_type 30 actx t T with
    | Except.ok _ =>
      let ctxE : Q(ACtx $n) := Lean.toExpr actx
      let tE : Q(ATm $n) := Lean.toExpr t
      let TE : Q(ATm $n) := Lean.toExpr T
      match ← whnf q(has_type 30 $ctxE $tE $TE) with
      | mkApp _ pr =>
        let ttm := mkApp5 (mkConst ``TTm.mk)
          (mkNatLit n)
          (← mkAppM ``ACtx.toCtx #[ctxE])
          (← mkAppM ``ATm.toTm #[tE])
          (← mkAppM ``ATm.toTm #[TE])
          (← mkAppM ``PLift.down #[pr])
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
      #guard_msgs(drop error) in
      theorem $id : ($ttm_id).Γ ⊢ ($ttm_id).t ∶ ($ttm_id).T := ($ttm_id).hasType)
