import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Weakening
import IMLTT.typed.annotated.Substitution

import Qq

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Command Qq Tactic

-- some parts of this file are heavily inspired by https://github.com/JLimperg/internal-language

def ElabCtx := List Name

namespace ElabCtx

protected def empty : ElabCtx := []

def extend (Γ : ElabCtx) (name : Name) : ElabCtx :=
  name :: Γ

def getFinIdx? (cx : ElabCtx) (name : Name) : Option ((n : Nat) × (Fin n)) :=
  cx.findFinIdx? (·==name) |>.map (⟨cx.length, ·⟩)

def toStr (cx : ElabCtx) : String := if cx.isEmpty then "ε" else
  String.intercalate ", " (cx.map toString)

def weakenCtx : {m : Nat} → (cx : ElabCtx) → (ρ : Weak m cx.length) → ElabCtx
  | _, cx, .id => cx
  | _, cx, .shift ρ' => Name.anonymous :: (weakenCtx cx ρ')
  | _, name :: rest, .lift ρ' => name :: (weakenCtx rest ρ')

def substituteCtx : {m : Nat} → (cx : ElabCtx) → (ρ : ASubst m cx.length) → ElabCtx
  | _, cx, .weak ρ' => weakenCtx cx ρ'
  | _, cx, .shift ρ' => Name.anonymous :: (substituteCtx cx ρ')
  | _, name :: rest, .lift ρ' => name :: (substituteCtx rest ρ')
  | _, _ :: rest, .extend ρ' _ => substituteCtx rest ρ'

end ElabCtx

partial def elabWeak (n : Nat) :  TSyntax `weak → TermElabM ((m : Nat) × (Weak m n))
  | `(weak| idₚ) => do
    return ⟨n, idₚ⟩
  | `(weak| ↑ₚ $w:weak) => do
    let ⟨m, ρ⟩ ← elabWeak (n-1) w
    logInfo m!"elabWeak: n={n}, m={m}"
    if h : n = n - 1 + 1 then
      return ⟨m + 1, h ▸ .lift ρ⟩
    else
      throwErrorAt w "Cannot shift weakening at context length 0"
  | `(weak| ⇑ₚ $w:weak) => do
    let ⟨m, ρ⟩ ← elabWeak n w
    return ⟨m + 1,.shift ρ⟩
  | `(weak| ↑₁ $w:weak ₙ⇑ₚ $i:num) => do
    let iVal := i.getNat
    let rec buildLift {m' n' : Nat} (k : Nat) (ρ : Weak m' n') : TermElabM (Weak (m' + k) (n' + k)) :=
      match k with
      | 0 => return ρ
      | k' + 1 => do
        let lifted ← buildLift k' ρ
        return .lift lifted
    let ⟨m,ρ⟩ ← elabWeak (n-iVal) w
    let lifted ← buildLift iVal ρ
    if h : n = n - iVal + iVal then
      return ⟨m + iVal, h ▸ lifted⟩
    else
      throwErrorAt w "Cannot shift weakening at context length 0"
  | _ => throwUnsupportedSyntax

def evalConstATm : Name → TermElabM (ATm 0) := fun id => do
  let info ← getConstInfo id
  let ttype ← instantiateMVars info.type
  if ← isDefEq ttype q(ATm 0) then
    unsafe evalConst (ATm 0) id
  else
    throwError "Constant '{id}' is not of type 'ATm 0'"

mutual
partial def elabSubst (cx : ElabCtx) : TSyntax `subst → TermElabM ((m: Nat) × (ASubst m cx.length))
  | `(subst| ₛ $w:weak) => do
    let ⟨m, ρ⟩ ← elabWeak cx.length w
    return ⟨m, .weak ρ⟩
  | `(subst| ↑ₛ $σ:subst) => do
    let ⟨m, ρ⟩ ← elabSubst (cx.drop 1) σ
    if h : cx.length = (cx.drop 1).length + 1 then
      return ⟨m + 1, h ▸ .lift ρ⟩
    else
      throwErrorAt σ "Cannot shift substitution at context length 0"
  | `(subst| ⇑ₛ $σ:subst) => do
    let ⟨m, ρ⟩ ← elabSubst cx σ
    return ⟨m + 1,.shift ρ⟩
  | `(subst| ₙ⇑ₛ $i:num $σ:subst) => do
    let iVal := i.getNat
    let rec buildLift {m' n' : Nat} (k : Nat) (ρ : ASubst m' n') : TermElabM (ASubst (m' + k) (n' + k)) :=
      match k with
      | 0 => return ρ
      | k' + 1 => do
        let lifted ← buildLift k' ρ
        return .lift lifted
    let ⟨m,ρ⟩ ← elabSubst (cx.drop iVal) σ
    let lifted ← buildLift iVal ρ
    if h : cx.length = (cx.drop iVal).length + iVal then
      return ⟨m + iVal, h ▸ lifted⟩
    else
      throwErrorAt σ "Cannot shift substitution at context length 0"
  | `(subst| $σ:subst ⋄ $t:atm) => do
    let ⟨m, ρ⟩ ← elabSubst (cx.drop 1) σ
    let substCx := ElabCtx.substituteCtx (cx.drop 1) ρ
    let ⟨nt, tE⟩ ← elabATm substCx t
    if h : nt = m ∧ cx.length = (cx.drop 1).length + 1 then
      let tE' : ATm m := h.left ▸ tE
      let extended := ASubst.extend ρ tE'
      return ⟨m, h.right ▸ extended⟩
    else
      throwErrorAt t "Term missmatch in substitution extension"
  | _ => throwUnsupportedSyntax

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
  | `(atm| 𝟘) => return ⟨cx.length, .empty⟩
  | `(atm| 𝟙) => return ⟨cx.length, .unit⟩
  | `(atm| 𝒩) => do return ⟨cx.length, .nat⟩
  | `(atm| 𝒰) => do return ⟨cx.length, .univ⟩
  | `(atm| $A:atm → $B:atm) => do
    let ⟨n, A'⟩ ← elabATm cx A
    let ⟨n', B'⟩ ← elabATm (cx.extend .anonymous) B
    if h : n+1 = n' then
      return ⟨n, ATm.pi A' <| h ▸ B'⟩
    else
      throwErrorAt B m!"Context length mismatch: expected {n'}+1, got {n}"
  | `(atm| Π ($id:ident : $A:atm; $B:atm)) => do
    let ⟨n, A'⟩ ← elabATm cx A
    let ⟨n', B'⟩ ← elabATm (cx.extend id.getId) B
    if h : n+1 = n' then
      return ⟨n, ATm.pi A' <| h ▸ B'⟩
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
  -- syntax "⋆" : atm
  | `(atm| ⋆) => do
    let n : Nat := cx.length
    return ⟨n, .tt⟩
  -- syntax "ind0" "(" ident atm atm ")": atm
  | `(atm| ind0 ($id:ident $P:atm $b:atm)) => do
    let ⟨nP, PE⟩ ← elabATm (cx.extend id.getId) P
    let ⟨nb, bE⟩ ← elabATm cx b
    if h : nb + 1 = nP then
      let PE' : ATm (nb+1) := h ▸ PE
      return ⟨nb, ATm.indEmpty PE' bE⟩
    else
      throwErrorAt P m!"Context length mismatch in ind𝟘: expected {nb}+1, got {nP}"
  -- syntax "ind1" "(" ident atm atm atm ")" : atm
  | `(atm| ind1($id:ident $P:atm $z:atm $c:atm)) => do
    let ⟨nP, PE⟩ ← elabATm (cx.extend id.getId) P
    let ⟨nz, zE⟩ ← elabATm cx z
    let ⟨nc, cE⟩ ← elabATm cx c
    if h : nP = nz + 1 ∧ nc = nz then
      let PE' : ATm (nz+1) := h.left ▸ PE
      let cE' : ATm nz := h.right ▸ cE
      return ⟨nz, ATm.indUnit PE' zE cE'⟩
    else
      throwErrorAt P m!"Context length mismatch in ind𝟙 motive: expected {nz}+1, got {nP}"
  -- syntax "λ " "(" ident " : " atm  ")" "." atm : atm
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
  -- syntax atm "◃" atm : atm
  | `(atm| $f:atm ◃ $a:atm) => do
    let ⟨n, fE⟩ ← elabATm cx f
    let ⟨n', aE⟩ ← elabATm cx a
    if h : n = n' then
      let aE' : (ATm n) := h ▸ aE
      let appE : (ATm n) := ATm.app fE aE'
      return ⟨n, appE⟩
    else
      throwErrorAt a m!"Term missmatch: expected context length {n}, got {n'}"
  -- syntax "(" atm "&" atm ")" "::" atm : atm
  | `(atm| ($a:atm & $b:atm) :: $B:atm) => do
    let ⟨n, aE⟩ ← elabATm cx a
    let ⟨n', bE⟩ ← elabATm cx b
    let ⟨n'', BE⟩ ← elabATm (cx.extend Name.anonymous) B
    if h : n = n' ∧ n + 1 = n'' then
      let bE' : ATm n := h.left ▸ bE
      let AE' : ATm (n+1) := h.right ▸ BE
      let pairE : ATm n := ATm.pairSigma aE bE' AE'
      return ⟨n, pairE⟩
    else
      throwErrorAt b m!"Term missmatch: expected context length {n}, got {n'} and {n''}"
  | `(atm| ($a:atm & $b:atm) :: $id → $B:atm) => do
    let ⟨n, aE⟩ ← elabATm cx a
    let ⟨n', bE⟩ ← elabATm cx b
    let ⟨n'', BE⟩ ← elabATm (cx.extend id.getId) B
    if h : n = n' ∧ n + 1 = n'' then
      let bE' : ATm n := h.left ▸ bE
      let AE' : ATm (n+1) := h.right ▸ BE
      let pairE : ATm n := ATm.pairSigma aE bE' AE'
      return ⟨n, pairE⟩
    else
      throwErrorAt b m!"Term missmatch: expected context length {n}, got {n'} and {n''}"
  -- syntax "indS" "(" ident ident ident atm atm atm atm atm ")" : atm
  | `(atm| indS($a:ident $b:ident $pid:ident $A:atm $B:atm $C:atm $c:atm $p:atm)) => do
    let ⟨n, tA⟩ ← elabATm cx A
    let ⟨nB, tB⟩ ← elabATm (cx.extend a.getId) B
    let ⟨nC, tC⟩ ← elabATm (cx.extend pid.getId) C
    let ⟨nc, tc⟩ ← elabATm (cx.extend a.getId |>.extend b.getId) c
    let ⟨np, tp⟩ ← elabATm cx p
    if h : n + 1 = nB ∧ n + 1 = nC ∧ n + 2 = nc ∧ n = np then
      let tB' : ATm (n+1) := h.left ▸ tB
      let tC' : ATm (n+1) := h.right.left ▸ tC
      let tc' : ATm (n+2) := h.right.right.left ▸ tc
      let tp' : ATm n := h.right.right.right ▸ tp
      return ⟨n, ATm.indSigma tA tB' tC' tc' tp'⟩
    else
      throwError m!"Context length mismatch in ind1"
  -- syntax "𝓏" : atm
  | `(atm| 𝓏) => do
    let n : Nat := cx.length
    return ⟨n, .zeroNat⟩
  -- syntax "𝓈(" atm ")" : atm
  | `(atm| 𝓈($t:atm)) => do
    let ⟨n, t⟩ ← elabATm cx t
    return ⟨n, .succNat t⟩
  -- syntax "indN" "(" ident ident atm atm atm atm ")" : atm
  | `(atm| indN($nId:ident $aId:ident $A:atm $z:atm $s:atm $n:atm)) => do
    let ⟨nA, tA⟩ ← elabATm (cx.extend nId.getId) A
    let ⟨nz, tz⟩ ← elabATm cx z
    let ⟨ns, ts⟩ ← elabATm (cx.extend aId.getId |>.extend aId.getId) s
    let ⟨nn, tn⟩ ← elabATm cx n
    if h : nz + 1 =  nA ∧ nz + 2  = ns ∧ nz = nn then
      let tA' : ATm (nz+1) := h.left ▸ tA
      let ts' : ATm (nz+2) := h.right.left ▸ ts
      let tn' : ATm nz := h.right.right ▸ tn
      return ⟨nz, ATm.indNat tA' tz ts' tn'⟩
    else
      throwError m!"Context length mismatch in indN"
  -- syntax "refl" "(" atm atm ")" : atm
  | `(atm| refl($A:atm $a:atm)) => do
    let ⟨nA, tA⟩ ← elabATm cx A
    let ⟨na, ta⟩ ← elabATm cx a
    if h : nA = na then
      let ta' : ATm nA := h ▸ ta
      return ⟨nA, ATm.refl tA ta'⟩
    else
      throwErrorAt a m!"Term missmatch in refl: expected context length {nA}, got {na}"
  -- syntax "j" "(" ident ident ident atm atm atm atm atm atm ")" : atm
  | `(atm| j ($AId:ident $AshiftId:ident $IdAId:ident $A:atm $B:atm $b:atm $a:atm $a':atm $p:atm)) => do
    let ⟨nA, tA⟩ ← elabATm cx A
    let ⟨nB, tB⟩ ← elabATm (cx.extend AId.getId |>.extend AshiftId.getId |>.extend IdAId.getId) B
    let ⟨nb, tb⟩ ← elabATm (cx.extend AId.getId) b
    let ⟨na, ta⟩ ← elabATm cx a
    let ⟨na', ta'⟩ ← elabATm cx a'
    let ⟨np, tp⟩ ← elabATm cx p
    if h : nA + 3 = nB ∧ nA +1 = nb ∧ nA = na ∧ nA = na' ∧ nA = np then
      let tB' : ATm (nA+3) := h.left ▸ tB
      let tb' : ATm (nA+1) := h.right.left ▸ tb
      let tap : ATm nA := h.right.right.left ▸ ta
      let ta'' : ATm nA := h.right.right.right.left ▸ ta'
      let tp' : ATm nA := h.right.right.right.right ▸ tp
      return ⟨nA, ATm.j tA tB' tb' tap ta'' tp'⟩
    else
      throwError m!"Context length mismatch in j"
  | `(atm| $t:atm ⌊$w:weak⌋) => do
    let ⟨n, tE⟩ ← elabATm cx t
    let ⟨mW, ρ⟩ ← elabWeak n w
    let tE' : ATm mW := (weaken' ρ tE)
    return ⟨mW, tE'⟩
  | `(atm| $t:atm ⌈$σ:subst⌉) => do
    let ⟨n, tE⟩ ← elabATm cx t
    let ⟨mS, ρ⟩ ← elabSubst cx σ
    if h : n = cx.length then
      let tE' : ATm mS := (substitute' ρ (h ▸ tE))
      return ⟨mS, tE'⟩
    throwError m!"Critical: Substitution context length mismatch: expected {cx.length}, got {n}"
  | `(atm| $t:atm ⌈$a:atm⌉₀) => do
    if cx.isEmpty then
      throwErrorAt a "Cannot perform zero substitution in empty context"
    let ⟨n, tE⟩ ← elabATm cx t
    -- this is a non-enforced invariant for non-empty contexts except for weakenings/substitutions
    let ⟨na, aE⟩ ← elabATm (cx.drop 1) a
    if h : n = na + 1 then
      let out := substitute_zero' aE (h ▸ tE)
      return ⟨na, out⟩
    throwErrorAt a "Term missmatch in zero substitution"
  | _ => throwUnsupportedSyntax
end

elab "[atm|" t:atm "]" : term => do
  let ⟨_, atm⟩ ← elabATm [] t
  return Lean.toExpr atm

def testunit : ATm 0 := [atm| 𝟙]
example : ATm 0 := [atm| λ (x : testunit). x]
example : ATm 0 := [atm| Π (x : 𝒰; x)]
example : ATm 0 := [atm| Π (x : 𝒰; x)⌈ₛidₚ⌉]
def subst_example : ATm 0 := [atm| Π (x : 𝒰; ((x)⌈𝟙⌉₀)⌊⇑ₚidₚ⌋)]
def app_assoc_example := [atm| λ (a : 𝒩). λ (b : 𝒰). λ (c : 𝒰). a ◃ b ◃ c]

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


elab "[acx|" Γ:actx "]" : term => do
  let ⟨_, ⟨_, actx⟩⟩ ← elabACtx [] Γ
  return Lean.toExpr actx

/-- info: ACtx.empty : ACtx 0 -/
#guard_msgs in
#check [acx| ε]
/--
info: ACtx.extend `z (ACtx.extend `y (ACtx.extend `x ACtx.empty ATm.unit) ATm.univ) (ATm.var 0) : ACtx (2 + 1)
-/
#guard_msgs in
#check [acx| ε ⬝ (x : 𝟙) ⬝ (y : 𝒰) ⬝ (z : y)]
