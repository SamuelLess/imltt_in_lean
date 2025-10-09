import IMLTT.untyped.AbstractSyntax
import Qq

open Lean

inductive ATm : Nat → Type where
  -- 'types'
  | unit : ATm n
  | empty : ATm n
  | pi : ATm n → ATm (n + 1) → ATm n
  | sigma : ATm n → ATm (n + 1) → ATm n
  | nat : ATm n
  | iden : ATm n → ATm n → ATm n → ATm n
  | univ : ATm n
  -- 'terms'
  | var : Fin n → ATm n -- added name and meaning of Fin n becomes stack height
  | tt : ATm n
  | indUnit : ATm (n + 1) → ATm n → ATm n → ATm n
  | indEmpty : ATm (n + 1) → ATm n → ATm n
  -- λx:A. b B where b⌈x⌉ : B⌈x⌉
  | lam : ATm n → ATm (n + 1) → ATm n -- added λ type annotation
  | app : ATm n → ATm n → ATm n
  -- a & b : Σ (dependent)
  | pairSigma : ATm n → ATm n → ATm n → ATm n -- add Σ type annotation
  -- (Γ ⊢ A) (Γ ⬝ A ⊢ B) ⬝ (Γ ⬝ ΣA;B ⊢ C) (Γ⬝ A ⬝ B ⊢ c : C) (Γ ⊢ p : ΣA;B)
  | indSigma: ATm n → ATm (n + 1) → ATm (n + 1) → ATm (n + 2) → ATm n → ATm n
  | zeroNat : ATm n
  | succNat : ATm n → ATm n
  | indNat : ATm (n + 1) → ATm n → ATm (n + 2) → ATm n → ATm n
  | refl : ATm n → ATm n → ATm n
  | j : ATm n → ATm (n + 3) → ATm (n + 1) → ATm n → ATm n → ATm n → ATm n
  deriving Repr, Nonempty, Lean.ToExpr

#check (ATm.var ⟨0, by omega⟩ : ATm (1))

def ATm.toTm {n} : ATm n → Tm n
  | .unit => Tm.unit
  | .empty => Tm.empty
  | .pi A B => Tm.pi (A.toTm) (B.toTm)
  | .sigma A B => Tm.sigma (A.toTm) (B.toTm)
  | .nat => Tm.nat
  | .iden A a b => Tm.iden (A.toTm) (a.toTm) (b.toTm)
  | .univ => Tm.univ
  | .var i => Tm.var i
  | .tt => Tm.tt
  | .indUnit P z c => Tm.indUnit (P.toTm) (z.toTm) (c.toTm)
  | .indEmpty P c => Tm.indEmpty (P.toTm) (c.toTm)
  | .lam A b => Tm.lam (A.toTm) (b.toTm)
  | .app f a => Tm.app (f.toTm) (a.toTm)
  | .pairSigma a b _ => Tm.pairSigma (a.toTm) (b.toTm)
  | .indSigma A P cs C p => Tm.indSigma (A.toTm) (P.toTm) (cs.toTm) (C.toTm) (p.toTm)
  | .zeroNat => Tm.zeroNat
  | .succNat n => Tm.succNat (n.toTm)
  | .indNat P z s n => Tm.indNat (P.toTm) (z.toTm) (s.toTm) (n.toTm)
  | .refl A a => Tm.refl (A.toTm) (a.toTm)
  | .j A P a b p r => Tm.j (A.toTm) (P.toTm) (a.toTm) (b.toTm) (p.toTm) (r.toTm)

theorem h : n + k + 1 = n + 1 + k := by omega
theorem h' : n + k + 2 = n + 2 + k := by omega
theorem h'' : n + k + 3 = n + 3 + k := by omega

def ATm.shift {n} (k : Nat) : ATm n → ATm (n + k)
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (A.shift k) (h ▸ (B.shift k))
  | .sigma A B => .sigma (A.shift k) (h ▸ B.shift k)
  | .nat => .nat
  | .iden A a b => .iden (A.shift k) (a.shift k) (b.shift k)
  | .univ => .univ
  --terms
  | .var i => .var ⟨i.1, by omega⟩
  | .tt => .tt
  | .indUnit P z c => .indUnit (h ▸ P.shift k) (z.shift k) (c.shift k)
  | .indEmpty P c => .indEmpty (h ▸ P.shift k) (c.shift k)
  | .lam A b => .lam (A.shift k) (h ▸ b.shift k)
  | .app f a => .app (f.shift k) (a.shift k)
  | .pairSigma a b A => .pairSigma (a.shift k) (b.shift k) (A.shift k)
  | .indSigma A P cs C p => .indSigma (A.shift k) (h ▸ P.shift k) (h ▸ cs.shift k) (h' ▸ C.shift k) (p.shift k)
  | .zeroNat => .zeroNat
  | .succNat n => .succNat (n.shift k)
  | .indNat P z s n => .indNat (h ▸ P.shift k) (z.shift k) (h' ▸ s.shift k) (n.shift k)
  | .refl A a => .refl (A.shift k) (a.shift k)
  | .j A P a b p r => .j (A.shift k) (h'' ▸ P.shift k) (h ▸ a.shift k) (b.shift k) (p.shift k) (r.shift k)

-- syntax for inductive Annotated Term type
declare_syntax_cat atm (behavior := both)

-- 'types'
syntax "𝟘" : atm
syntax "𝟙" : atm
syntax "𝒩" : atm
syntax "𝒰" : atm
syntax atm " → " atm : atm -- nondependent Pi type
syntax "Π" "(" ident ":" atm ";"  atm ")" : atm
syntax "Σ" "(" ident ":" atm ";"  atm ")" : atm
-- 'terms'
syntax "(" atm ")" : atm
syntax ident : atm
syntax "⋆" : atm
syntax "ind0" "(" ident atm atm ")": atm
syntax "ind1" "(" ident atm atm atm ")" : atm
syntax "λ " "(" ident " : " atm  ")" "." atm : atm
syntax atm "◃" atm : atm
syntax "(" atm "&" atm ")" "::" atm : atm
syntax "indS" "(" ident ident ident atm atm atm atm atm ")" : atm
syntax "𝓏" : atm
syntax "𝓈(" atm ")" : atm
syntax "indN" "(" ident ident atm atm atm atm ")" : atm
syntax "refl" "(" atm atm ")" : atm
syntax "j" "(" ident ident ident atm atm atm atm atm atm ")" : atm
syntax atm "⌈" term "⌉" : atm
syntax atm "⌊" term "⌋" : atm

#check_failure `(atm|𝟙 → 𝟙)
#check_failure `(atm|Π(x : 𝟙;𝟙))
#check_failure `(atm|Σ(x : 𝒰;x))
#check_failure `(atm| ind0(a P b))
#check_failure `(atm| indS(a b p A B C c p))

inductive ACtx : Nat → Type where
  | empty : ACtx 0
  | extend : Name → ACtx n → ATm n → ACtx (n + 1)
  deriving Repr, Lean.ToExpr

def ACtx.toCtx {n} : ACtx n → Ctx n
  | .empty => Ctx.empty
  | .extend _ Γ T => Ctx.extend (Γ.toCtx) (T.toTm)

def ACtx.toNameList : ACtx n → List Name
  | .empty => []
  | .extend name Γ _ => name :: Γ.toNameList

declare_syntax_cat actx (behavior := both)

syntax "ε" : actx
syntax actx "⬝" "(" ident ":" atm ")" : actx

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
  | `(atm| $A:atm → $B:atm) => do
    let ⟨n, AE⟩ ← elabATm cx A
    let ⟨n', BE⟩ ← elabATm (cx.extend Name.anonymous) B
    --if ← isDefEq q($n') q($n+1) then
    if h : n+1 = n' then
      let bbE : (ATm (n+1)) := h ▸ BE
      let piE : (ATm n) := ATm.pi AE bbE
      return ⟨n, piE⟩
    else
      throwErrorAt B m!"Context length mismatch: expected {n'}+1, got {n}"
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


elab "[acx|" Γ:actx "]" : term => do
  let ⟨_, ⟨_, actx⟩⟩ ← elabACtx [] Γ
  return Lean.toExpr actx

#check [acx| ε]
#check [acx| ε ⬝ (x : 𝟙) ⬝ (y : 𝒰) ⬝ (z : y)]
