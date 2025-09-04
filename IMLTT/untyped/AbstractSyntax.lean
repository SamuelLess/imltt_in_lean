import Lean.ToExpr

inductive Tm : Nat → Type where
  -- 'types'
  | unit : Tm n
  | empty : Tm n
  | pi : Tm n → Tm (n + 1) → Tm n
  | sigma : Tm n → Tm (n + 1) → Tm n
  | nat : Tm n
  | iden : Tm n → Tm n → Tm n → Tm n
  | univ : Tm n
  -- 'terms'
  | var : Fin n → Tm n
  | tt : Tm n
  | indUnit : Tm (n + 1) → Tm n → Tm n → Tm n
  | indEmpty : Tm (n + 1) → Tm n → Tm n
  | lam : Tm n → Tm (n + 1) → Tm n
  | app : Tm n → Tm n → Tm n
  | pairSigma : Tm n → Tm n → Tm n
  | indSigma: Tm n → Tm (n + 1) → Tm (n + 1) → Tm (n + 2) → Tm n → Tm n
  | zeroNat : Tm n
  | succNat : Tm n → Tm n
  | indNat : Tm (n + 1) → Tm n → Tm (n + 2) → Tm n → Tm n
  | refl : Tm n → Tm n → Tm n
  | j : Tm n → Tm (n + 3) → Tm (n + 1) → Tm n → Tm n → Tm n → Tm n
deriving BEq, Repr, Lean.ToExpr

inductive Ctx : Nat → Type where
  | empty : Ctx 0
  | extend : Ctx n → Tm n → Ctx (n + 1)
deriving BEq, Repr, Lean.ToExpr

-- types
notation:max "𝟙" => Tm.unit
notation:max "𝟘" => Tm.empty
notation:98 "Π" A ";" B => Tm.pi A B
notation:98 "Σ" A ";" B => Tm.sigma A B
notation:max "𝒩" => Tm.nat
notation:98 s " ≃" "[" A "] " t => Tm.iden A s t
notation:max "𝒰" => Tm.univ
-- terms
notation:max "v(" x ")" => Tm.var x
notation:max "⋆" => Tm.tt
notation:98 "λ" A "; " b => Tm.lam A b
infixl:98 "◃" => Tm.app
infixl:98 "&" => Tm.pairSigma
notation:max "𝓏" => Tm.zeroNat
notation:max "𝓈(" x ")" => Tm.succNat x


notation:max "ε" => Ctx.empty
infixl:94 " ⬝ " => Ctx.extend

instance : Coe (Fin n) (Tm n) where
  coe n := .var n

def Tm.toString : Tm n → String
  | Tm.unit => "𝟙"
  | Tm.empty => "𝟘"
  | Tm.pi A B => s!"Π{A.toString};{B.toString}"
  | Tm.sigma A B => s!"Σ{A.toString};{B.toString}"
  | Tm.nat => "𝒩"
  | Tm.iden A s t => s!"{s.toString}≃[{A.toString}]{t.toString}"
  | Tm.univ => "𝒰"
  | Tm.var n => s!"v({n})"
  | Tm.tt => "⋆"
  | Tm.lam A b => s!"λ{A.toString};{b.toString}"
  | Tm.app f a => s!"{f.toString}◃{a.toString}"
  | Tm.pairSigma a b => s!"{a.toString}&{b.toString}"
  | Tm.zeroNat => "𝓏"
  | Tm.succNat a => s!"𝓈({a.toString})"
  | Tm.indUnit A b c => s!"indUnit {A.toString} {b.toString} {c.toString}"
  | Tm.indEmpty A b => s!"indEmpty {A.toString} {b.toString}"
  | Tm.indSigma A B C D E => s!"indSigma {A.toString} {B.toString} {C.toString}
      {D.toString} {E.toString}"
  | Tm.refl A B => s!"refl({A.toString},{B.toString})"
  | Tm.indNat A b c d => s!"indNat {A.toString} {b.toString} {c.toString} {d.toString}"
  | Tm.j A B C D E F => s!"j {A.toString} {B.toString} {C.toString}
    {D.toString} {E.toString} {F.toString}"

instance : ToString (Tm n) where
  toString := Tm.toString
