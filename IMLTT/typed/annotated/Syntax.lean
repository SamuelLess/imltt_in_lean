import IMLTT.untyped.AbstractSyntax

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
  -- a & b : B (as non substituted) (dependent)
  | pairSigma : ATm n → ATm n → ATm (n+1) → ATm n -- add Σ type annotation
  -- (Γ ⊢ A) (Γ ⬝ A ⊢ B) ⬝ (Γ ⬝ ΣA;B ⊢ C) (Γ⬝ A ⬝ B ⊢ c : C) (Γ ⊢ p : ΣA;B)
  | indSigma: ATm n → ATm (n + 1) → ATm (n + 1) → ATm (n + 2) → ATm n → ATm n
  | zeroNat : ATm n
  | succNat : ATm n → ATm n
  | indNat : ATm (n + 1) → ATm n → ATm (n + 2) → ATm n → ATm n
  | refl : ATm n → ATm n → ATm n
  | j : ATm n → ATm (n + 3) → ATm (n + 1) → ATm n → ATm n → ATm n → ATm n
  deriving Repr, Nonempty, Lean.ToExpr

/-- info: ATm.var ⟨0, ⋯⟩ : ATm 1 -/
#guard_msgs in
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
  | .pairSigma a b B => .pairSigma (a.shift k) (b.shift k) (h ▸ B.shift k)
  | .indSigma A P cs C p => .indSigma (A.shift k) (h ▸ P.shift k) (h ▸ cs.shift k) (h' ▸ C.shift k) (p.shift k)
  | .zeroNat => .zeroNat
  | .succNat n => .succNat (n.shift k)
  | .indNat P z s n => .indNat (h ▸ P.shift k) (z.shift k) (h' ▸ s.shift k) (n.shift k)
  | .refl A a => .refl (A.shift k) (a.shift k)
  | .j A P a b p r => .j (A.shift k) (h'' ▸ P.shift k) (h ▸ a.shift k) (b.shift k) (p.shift k) (r.shift k)


def ATm.toString {n}  (atm : ATm n) : String := (atm.toTm).toString

instance {n} : ToString (ATm n) where
  toString := ATm.toString

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
syntax "(" atm "&" atm ")" "::" ident "→" atm : atm
syntax "indS" "(" ident ident ident atm atm atm atm atm ")" : atm
syntax "𝓏" : atm
syntax "𝓈(" atm ")" : atm
syntax "indN" "(" ident ident atm atm atm atm ")" : atm
syntax "refl" "(" atm atm ")" : atm
syntax "j" "(" ident ident ident atm atm atm atm atm atm ")" : atm

declare_syntax_cat weak (behavior := both)
syntax atm "⌊" weak "⌋" : atm
syntax "idₚ" : weak
syntax "↑ₚ" weak : weak
syntax "⇑ₚ" weak : weak
syntax "ₙ⇑ₚ" num weak : weak
syntax "↑₁" weak "ₙ⇑ₚ" num : weak

declare_syntax_cat subst (behavior := both)
syntax "ₛ" weak : subst
syntax "↑ₛ" subst : subst
syntax "⇑ₛ" subst : subst
syntax "ₙ⇑ₛ" num subst : subst
syntax subst "⋄" atm : subst
syntax atm "⌈" subst "⌉" : atm
syntax atm "⌈" atm "⌉₀" : atm

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

def ACtx.toString {n} : ACtx n → String
  | .empty => "ε"
  | .extend name Γ T => s!"{Γ.toString} ⬝ ({name} : {T.toTm})"

instance : ToString (ACtx n) where
  toString := ACtx.toString

declare_syntax_cat actx (behavior := both)

syntax "ε" : actx
syntax actx "⬝" "(" ident ":" atm ")" : actx

theorem toCtx_extend {n} (Γ : ACtx n) (x : Name) (T : ATm n) :
    (Γ.extend x  T).toCtx = (Γ.toCtx).extend T.toTm := by
  simp [ACtx.toCtx]
