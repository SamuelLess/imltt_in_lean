import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Elaboration
import IMLTT.typed.checked.TypeChecker

import Qq

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command Qq Tactic

def fuel := 50 -- proof go brrr 🚗

-- Γ ctx
structure InstIsCtx (n : Nat) where
  Γ : Ctx n
  isCtx : Γ ctx

partial def elabIsCtx (stxcx : TSyntax `actx) :
    TermElabM Q((n : Nat) × InstIsCtx n) := do
  let ⟨_, ⟨n, actx⟩⟩ ← elabACtx [] stxcx
  match is_ctx (is_type fuel) actx with
  | Except.ok _ =>
    let ctxE : Q(ACtx $n) := Lean.toExpr actx
    match ← whnf q(is_ctx (is_type fuel) $ctxE) with
    | .app _ pr =>
      let ttm := mkApp3 (mkConst ``InstIsCtx.mk)
        (mkNatLit n)
        (← mkAppM ``ACtx.toCtx #[ctxE])
        (← mkAppM ``PLift.down #[pr])
      return ttm
    | _ => unreachable!
  | Except.error msg =>
    throwErrorAt stxcx "Type error: {msg}"

elab "[tcx|" cx:actx"]" : term => elabIsCtx cx
example : [tcx| ε] = ⟨ε, by constructor⟩ := rfl
def test_tcx := [tcx| ε ⬝ (b : 𝒩)]

-- Γ ⊢ A type
structure InstIsType (n : Nat) where
  Γ : Ctx n
  T : Tm n
  isType : Γ ⊢ T type

partial def elabIsType (stxcx : TSyntax `actx) (stxT : TSyntax `atm) :
    TermElabM Q((n : Nat) × InstIsType n) := do
  let ⟨cx, ⟨n, actx⟩⟩ ← elabACtx [] stxcx
  let ⟨nT, aTm⟩ ← elabATm cx stxT
  if h : n = nT then
    let T : ATm n := h ▸ aTm
    match is_type fuel n actx T with
    | Except.ok _ =>
      let ctxE : Q(ACtx $n) := Lean.toExpr actx
      let TE : Q(ATm $n) := Lean.toExpr T
      match ← whnf q(is_type fuel _ $ctxE $TE) with
      | .app _ pr =>
        let ttm := mkApp4 (mkConst ``InstIsType.mk)
          (mkNatLit n)
          (← mkAppM ``ACtx.toCtx #[ctxE])
          (← mkAppM ``ATm.toTm #[TE])
          (← mkAppM ``PLift.down #[pr])
        return ttm
      | _ => unreachable!
    | Except.error msg =>
      throwErrorAt stxT "Type error: {msg}"
  else throwErrorAt stxT m!"Context length mismatch: expected {n}, got {nT}"

elab "[tit|" cx:actx "⊢" T:atm "type" "]" : term => elabIsType cx T
def test_tit := [tit| ε ⊢ 𝒩 type]
def test_tit' := [tit| ε ⬝ (T : 𝒰) ⊢ T type]

-- Γ ⊢ a : A
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
    match has_type fuel actx t T with
    | Except.ok _ =>
      let ctxE : Q(ACtx $n) := Lean.toExpr actx
      let tE : Q(ATm $n) := Lean.toExpr t
      let TE : Q(ATm $n) := Lean.toExpr T
      match ← whnf q(has_type fuel $ctxE $tE $TE) with
      | .app _ pr =>
        return mkApp5 (mkConst ``InstHasType.mk)
          (mkNatLit n)
          (← mkAppM ``ACtx.toCtx #[ctxE])
          (← mkAppM ``ATm.toTm #[tE])
          (← mkAppM ``ATm.toTm #[TE])
          (← mkAppM ``PLift.down #[pr])
      | _ => unreachable!
    | Except.error msg =>
      throwErrorAt stxt "Type error: {msg}"
  else throwErrorAt stxt
    m!"Context length mismatch: expected {n} (context), got {nt} (term) and {nT} (type)"

elab "[tht|" cx:actx "⊢" t:atm ":" T:atm "]" : term => elabHasType cx t T

def test1 := [tht| ε ⊢ ⋆ : 𝟙]
/-
/-- error: Type error: is_eq_type: out of fuel 𝒰 ≡ 𝟙 -/
#guard_msgs in-/
--def test2 := [tht| ε ⊢ ⋆ : 𝒰]
def test3 := [tht| ε ⊢ 𝓈(𝓏) : 𝒩]

-- - Γ ⊢ A = A' type
structure InstIsEqualType (n : Nat) where
  Γ : Ctx n
  T : Tm n
  T' : Tm n
  isEqualType : Γ ⊢ T ≡ T' type

partial def elabIsEqualType (stxcx : TSyntax `actx) (stxT stxT' : TSyntax `atm) :
    TermElabM Q((n : Nat) × InstIsEqualType n) := do
  let ⟨cx, ⟨n, actx⟩⟩ ← elabACtx [] stxcx
  let ⟨nT, aTm⟩ ← elabATm cx stxT
  let ⟨nT', aTm'⟩ ← elabATm cx stxT'
  if h : n = nT ∧ n = nT' then
    let T : ATm n := h.left ▸ aTm
    let T' : ATm n := h.right ▸ aTm'
    match is_eq_type fuel actx T T' with
    | Except.ok _ =>
      let ctxE : Q(ACtx $n) := Lean.toExpr actx
      let TE : Q(ATm $n) := Lean.toExpr T
      let TE' : Q(ATm $n) := Lean.toExpr T'
      match ← whnf q(is_eq_type fuel $ctxE $TE $TE') with
      | .app _ pr =>
        let ttm := mkApp5 (mkConst ``InstIsEqualType.mk)
          (mkNatLit n)
          (← mkAppM ``ACtx.toCtx #[ctxE])
          (← mkAppM ``ATm.toTm #[TE])
          (← mkAppM ``ATm.toTm #[TE'])
          (← mkAppM ``PLift.down #[pr])
        return ttm
      | _ => unreachable!
    | Except.error msg =>
      throwErrorAt stxT "Type error: {msg}"
  else throwErrorAt stxT m!"Context length mismatch: expected {n}, got {nT} and {nT'}"

elab "[tieT|" cx:actx "⊢" T:atm "≡" T':atm "type" "]" : term => elabIsEqualType cx T T'
def test_tieT := [tieT| ε ⊢ 𝟙 ≡ 𝟙 type]
def test_tieT' := [tieT| ε ⬝ (A : 𝒰) ⊢ A ≡ A type]

-- Γ ⊢ a = a' : A
structure InstIsEqualTerm (n : Nat) where
  Γ : Ctx n
  t : Tm n
  t' : Tm n
  T : Tm n
  isEqualTerm : Γ ⊢ t ≡ t' ∶ T

partial def elabIsEqualTerm (stxcx : TSyntax `actx) (stxt stxt' stxT : TSyntax `atm) :
    TermElabM Q((n : Nat) × InstIsEqualTerm n) := do
  let ⟨cx, ⟨n, actx⟩⟩ ← elabACtx [] stxcx
  let ⟨nt, atm⟩ ← elabATm cx stxt
  let ⟨nt', atm'⟩ ← elabATm cx stxt'
  let ⟨nT, aTm⟩ ← elabATm cx stxT
  if h : n = nt ∧ n = nt' ∧ n = nT then
    let t : ATm n := h.left ▸ atm
    let t' : ATm n := h.right.left ▸ atm'
    let T : ATm n := h.right.right ▸ aTm
    match is_eq_term fuel actx t t' T with
    | Except.ok _ =>
      let ctxE : Q(ACtx $n) := Lean.toExpr actx
      let tE : Q(ATm $n) := Lean.toExpr t
      let tE' : Q(ATm $n) := Lean.toExpr t'
      let TE : Q(ATm $n) := Lean.toExpr T
      match ← whnf q(is_eq_term fuel $ctxE $tE $tE' $TE) with
      | .app _ pr =>
        let ttm := mkApp6 (mkConst ``InstIsEqualTerm.mk)
          (mkNatLit n)
          (← mkAppM ``ACtx.toCtx #[ctxE])
          (← mkAppM ``ATm.toTm #[tE])
          (← mkAppM ``ATm.toTm #[tE'])
          (← mkAppM ``ATm.toTm #[TE])
          (← mkAppM ``PLift.down #[pr])
        return ttm
      | _ => unreachable!
    | Except.error msg =>
      throwErrorAt stxT "Type error: {msg}"
  else throwErrorAt stxcx m!"Context length mismatch: expected {n}, got {nt}, {nt'}, and {nT}"

elab "[tiet|" cx:actx "⊢" t:atm "≡" t':atm ":" T:atm "]" : term => elabIsEqualTerm cx t t' T
def test_tiet := [tiet| ε ⊢ ⋆ ≡ ⋆ : 𝟙]
def test_tiet' := [tiet| ε ⬝ (n : 𝒩) ⊢ n ≡ n : 𝒩]

/-- Elaborate the instance `def`; only elaborate the `theorem` if the `def`
succeeded, so a type error surfaces once instead of causing cascade errors. -/
def elabTTheoremCmds (defCmd thmCmd : TSyntax `command) : CommandElabM Unit := do
  let hadErrors := (← get).messages.hasErrors
  elabCommand defCmd
  if hadErrors || !(← get).messages.hasErrors then
    elabCommand thmCmd

elab "ttheorem " id:ident " : " cx:actx "ctx" : command => do
  let var_ident := mkIdent <| Name.str id.getId "_InstIsCtx"
  elabTTheoremCmds
    (← `(@[reducible] def $var_ident:ident := [tcx| $cx]))
    (← `(theorem $id : ($var_ident).Γ ctx := ($var_ident).isCtx))

elab "ttheorem " id:ident " : " cx:actx "⊢" T:atm "type" : command => do
  let var_ident := mkIdent <| Name.str id.getId "_InstIsType"
  elabTTheoremCmds
    (← `(@[reducible] def $var_ident:ident := [tit| $cx ⊢ $T type]))
    (← `(theorem $id : ($var_ident).Γ ⊢ ($var_ident).T type := ($var_ident).isType))

elab "ttheorem " id:ident " : " cx:actx "⊢" t:atm ":" T:atm : command => do
  let var_ident := mkIdent <| Name.str id.getId "_InstHasType"
  elabTTheoremCmds
    (← `(@[reducible] def $var_ident:ident := [tht| $cx ⊢ $t : $T]))
    (← `(theorem $id : ($var_ident).Γ ⊢ ($var_ident).t ∶ ($var_ident).T := ($var_ident).hasType))

elab "ttheorem " id:ident " : " cx:actx "⊢" T:atm "≡" T':atm "type" : command => do
  let var_ident := mkIdent <| Name.str id.getId "_InstIsEqualType"
  elabTTheoremCmds
    (← `(@[reducible] def $var_ident:ident := [tieT| $cx ⊢ $T ≡ $T' type]))
    (← `(theorem $id : ($var_ident).Γ ⊢ ($var_ident).T ≡ ($var_ident).T' type := ($var_ident).isEqualType))

elab "ttheorem " id:ident " : " cx:actx "⊢" t:atm "≡" t':atm ":" T:atm : command => do
  let var_ident := mkIdent <| Name.str id.getId "_InstIsEqualTerm"
  elabTTheoremCmds
    (← `(@[reducible] def $var_ident:ident := [tiet| $cx ⊢ $t ≡ $t' : $T]))
    (← `(theorem $id : ($var_ident).Γ ⊢
      ($var_ident).t ≡ ($var_ident).t' ∶ ($var_ident).T := ($var_ident).isEqualTerm))
