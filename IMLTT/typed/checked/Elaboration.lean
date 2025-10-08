import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.checked.TypeChecker
import IMLTT.typed.AnnotatedSyntax
import Qq

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command Qq Tactic

def ElabCtx := List Name

namespace ElabCtx

protected def empty : ElabCtx := []

def extend (Γ : ElabCtx) (name : Name) : ElabCtx :=
  name :: Γ

def getFinIdx? (cx : ElabCtx) (name : Name) : Option ((n : Nat) × (Fin n)) :=
  cx.findFinIdx? (·==name) |>.map (⟨cx.length, ·⟩)

def toStr (cx : ElabCtx) : String := if cx.isEmpty then "ε" else
  String.intercalate ", " (cx.map toString)

end ElabCtx

def evalConstATm : Name → TermElabM (ATm 0) := fun id => do
  let info ← getConstInfo id
  let ttype ← instantiateMVars info.type
  if ← isDefEq ttype q(ATm 0) then
    unsafe evalConst (ATm 0) id
  else
    throwError "Constant '{id}' is not of type 'ATm 0'"

partial def elabATm (cx : ElabCtx): TSyntax `atm → TermElabM ((n : Nat) × ATm n)
  | `(atm| $id:ident) => do
    let id' := id.getId
    if let some ⟨n, i⟩ := cx.getFinIdx? id' then
      return ⟨n, ATm.var i⟩
    else
      try
        let myterm : ATm 0 ← evalConstATm id'
        let n := cx.length
        return ⟨n, (Nat.zero_add n) ▸ (myterm.shift n)⟩
      catch _ => throwErrorAt id "Unexpected identifier '{id'}', context: {cx.toStr}"
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
      let bbE : (ATm (n+1)) := h ▸ BE
      let piE : (ATm n) := ATm.pi AE bbE
      return ⟨n, piE⟩
    else
      throwErrorAt B m!"Context length mismatch: expected {n'}+1, got {n}"
  | `(atm| Σ ($id:ident : $A:atm; $B:atm)) => do
    let ⟨n, AE⟩ ← elabATm cx A
    let id' := id.getId
    let ⟨n', BE⟩ ← elabATm (cx.extend id') B
    if h : n+1 = n' then
      let bbE : (ATm (n+1)) := h ▸ BE
      let sigmaE : (ATm n) := ATm.sigma AE bbE
      return ⟨n, sigmaE⟩
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
  | `(atm| $f:atm $a:atm) => do
    let ⟨n, fE⟩ ← elabATm cx f
    let ⟨n', aE⟩ ← elabATm cx a
    if h : n = n' then
      let aE' : (ATm n) := h ▸ aE
      let appE : (ATm n) := ATm.app fE aE'
      return ⟨n, appE⟩
    else
      throwErrorAt a m!"Term missmatch: expected context length {n}, got {n'}"
  | `(atm| ($a:atm & $b:atm) :: $A:atm) => do
    let ⟨n, aE⟩ ← elabATm cx a
    let ⟨n', bE⟩ ← elabATm cx b
    let ⟨n'', AE⟩ ← elabATm cx A
    if h : n = n' ∧ n = n'' then
      let bE' : (ATm n) := h.left ▸ bE
      let AE' : (ATm n) := h.right ▸ AE
      let pairE : (ATm n) := ATm.pairSigma aE bE' AE'
      return ⟨n, pairE⟩
    else
      throwErrorAt b m!"Term missmatch: expected context length {n}, got {n'} and {n''}"
  | _ => throwUnsupportedSyntax

elab "[atm|" t:atm "]" : term => do
  let ⟨_, atm⟩ ← elabATm [] t
  return Lean.toExpr atm

def testunit : ATm 0 := [atm| 𝟙]
example : ATm 0 := [atm| λ (x : testunit). x]
example : ATm 0 := [atm| Π (x : 𝒰; x)]

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
      #guard_msgs(drop error) in
      theorem $id : ($ttm_id).Γ ⊢ ($ttm_id).t ∶ ($ttm_id).T := ($ttm_id).hasType)
