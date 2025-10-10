import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Elaboration
import IMLTT.typed.checked.TypeChecker

import Qq

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command Qq Tactic

-- - Γ ctx
structure InstIsCtx (n : Nat) where
  Γ : Ctx n
  hasType : Γ ctx

partial def elabIsCtx (stxcx : TSyntax `actx) :
    TermElabM Q((n : Nat) × InstIsCtx n) := do
  let ⟨_, ⟨n, actx⟩⟩ ← elabACtx [] stxcx
  match is_ctx (is_type 30) actx with
  | Except.ok _ =>
    let ctxE : Q(ACtx $n) := Lean.toExpr actx
    match ← whnf q(is_ctx (is_type 30) $ctxE) with
    | mkApp _ pr =>
      let ttm := mkApp3 (mkConst ``InstIsCtx.mk)
        (mkNatLit n)
        (← mkAppM ``ACtx.toCtx #[ctxE])
        (← mkAppM ``PLift.down #[pr])
      return ttm
    | _ => throwError "Could not find proof again o.O"
  | Except.error msg =>
    throwErrorAt stxcx "Type error: { msg }"

elab "[tcx|" cx:actx"]" : term => elabIsCtx cx
example : [tcx| ε] = ⟨ε, by constructor⟩ := rfl
def test_tcx := [tcx| ε ⬝ (n : 𝒩)]

-- - Γ ⊢ A type
structure InstIsType (n : Nat) where
  Γ : Ctx n
  T : Tm n
  hasType : Γ ⊢ T type

partial def elabIsType (stxcx : TSyntax `actx) (stxT : TSyntax `atm) :
    TermElabM Q((n : Nat) × InstIsType n) := do
  let ⟨cx, ⟨n, actx⟩⟩ ← elabACtx [] stxcx
  let ⟨nT, aTm⟩ ← elabATm cx stxT
  if h : n = nT then
    let T : ATm n := h ▸ aTm
    match is_type 30 n actx T with
    | Except.ok _ =>
      let ctxE : Q(ACtx $n) := Lean.toExpr actx
      let TE : Q(ATm $n) := Lean.toExpr T
      match ← whnf q(is_type 30 _ $ctxE $TE) with
      | mkApp _ pr =>
        let ttm := mkApp4 (mkConst ``InstIsType.mk)
          (mkNatLit n)
          (← mkAppM ``ACtx.toCtx #[ctxE])
          (← mkAppM ``ATm.toTm #[TE])
          (← mkAppM ``PLift.down #[pr])
        return ttm
      | _ => throwError "Could not find proof again o.O"
    | Except.error msg =>
      throwErrorAt stxT "Type error: { msg }"
  else throwErrorAt stxT m!"Context length mismatch: expected {n}, got {nT}"

elab "[tit|" cx:actx "⊢" T:atm "type" "]" : term => elabIsType cx T
def test_tit := [tit| ε ⊢ 𝒩 type]
def test_tit' := [tit| ε ⬝ (T : 𝒰) ⊢ T type]

-- - Γ ⊢ a : A
structure InstHasType (n : Nat) where
  Γ : Ctx n
  t : Tm n
  T : Tm n
  hasType : Γ ⊢ t ∶ T

partial def elabHasType (stxcx : TSyntax `actx) (stxt stxT : TSyntax `atm) :
    TermElabM Q((n : Nat) × InstHasType n) := do
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
        let ttm := mkApp5 (mkConst ``InstHasType.mk)
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

elab "[tht|" cx:actx "⊢" t:atm ":" T:atm "]" : term => elabHasType cx t T

def test1 := [tht| ε ⊢ ⋆ : 𝟙]
/-- error: Type error: is_eq_type: out of fuel 𝒰 ≡ 𝟙 -/
#guard_msgs in
def test2 := [tht| ε ⊢ ⋆ : 𝒰]
def test3 := [tht| ε ⊢ 𝓈(𝓏) : 𝒩]

-- - Γ ⊢ A = A' type
structure InstIsEqualType (n : Nat) where
  Γ : Ctx n
  T : Tm n
  T' : Tm n
  hasType : Γ ⊢ T ≡ T type

-- TODO: add elab for IsEqualType

-- - Γ ⊢ a = a' : A
structure InstIsEqualTerm (n : Nat) where
  Γ : Ctx n
  t : Tm n
  t' : Tm n
  T : Tm n
  hasType : Γ ⊢ t ≡ t' ∶ T

syntax "ttheorem " ident " : " actx "⊢" atm ":" atm : command
macro_rules
  | `(ttheorem $id:ident : $cx:actx ⊢ $t:atm : $T:atm) => do
    let ttm_name := Name.str id.getId "_TTm"
    let ttm_id := mkIdent ttm_name
    `(def $ttm_id:ident := [tht| $cx ⊢ $t : $T]
      #guard_msgs(drop error) in
      theorem $id : ($ttm_id).Γ ⊢ ($ttm_id).t ∶ ($ttm_id).T := ($ttm_id).hasType)
