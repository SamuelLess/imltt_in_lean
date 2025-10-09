import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Weakening
import IMLTT.untyped.Substitution

inductive ASubst : Nat → Nat → Type where
  | weak : Weak m n → ASubst m n
  | shift : ASubst m n → ASubst (m + 1) n
  | lift : ASubst m n → ASubst (m + 1) (n + 1)
  | extend : ASubst m n → ATm m → ASubst m (n + 1)

@[simp]
def substitute_var' (σ : ASubst m n) (x : Fin n) : ATm m :=
  match σ with
  | .weak ρ => .var <| weaken_var ρ x
  | .shift σ' => shift_tm' (substitute_var' σ' x)
  | .lift σ' =>
    match x with
    | ⟨0, _⟩ => .var (.mk 0 (by simp []))
    | ⟨x' + 1, h⟩ => shift_tm' (substitute_var' σ' (.mk x' (by simp [Nat.lt_of_succ_lt_succ h])))
  | .extend σ' t =>
    match x with
    | ⟨0, _⟩ => t
    | ⟨x' + 1, h⟩ => substitute_var' σ' (.mk x' (Nat.lt_of_succ_lt_succ h))

@[simp]
def lift_subst_n' (i : Nat) (σ : ASubst m n) : ASubst (m + i) (n + i) :=
  match i with
  | 0 => σ
  | i' + 1 => .lift (lift_subst_n' i' σ)

@[simp]
def substitute' (σ : ASubst m n) (t : ATm n) : ATm m :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (substitute' σ A) (substitute' (lift_subst_n' 1 σ) B)
  | .sigma A B => .sigma (substitute' σ A) (substitute' (lift_subst_n' 1 σ) B)
  | .nat => .nat
  | .iden A a a' => .iden (substitute' σ A) (substitute' σ a) (substitute' σ a')
  | .univ => .univ
  | .var i => substitute_var' σ i
  | .tt => .tt
  | .indUnit A b a => .indUnit (substitute' (lift_subst_n' 1 σ) A) (substitute' σ b) (substitute' σ a)
  | .indEmpty A b => .indEmpty (substitute' (lift_subst_n' 1 σ) A) (substitute' σ b)
  | .lam A b => .lam (substitute' σ A) (substitute' (lift_subst_n' 1 σ) b)
  | .app f a => .app (substitute' σ f) (substitute' σ a)
  | .pairSigma a b S => .pairSigma (substitute' σ a) (substitute' σ b) (substitute' σ S)
  | .indSigma A B C c p => .indSigma (substitute' σ A) (substitute' (lift_subst_n' 1 σ) B)
                            (substitute' (lift_subst_n' 1 σ) C) (substitute' (lift_subst_n' 2 σ) c)
                            (substitute' σ p)
  | .zeroNat => .zeroNat
  | .succNat x => .succNat (substitute' σ x)
  | .indNat A z s n => .indNat (substitute' (lift_subst_n' 1 σ) A) (substitute' σ z)
                        (substitute' (lift_subst_n' 2 σ) s) (substitute' σ n)
  | .refl A a => .refl (substitute' σ A) (substitute' σ a)
  | .j A B b a a' p => .j (substitute' σ A) (substitute' (lift_subst_n' 3 σ) B)
                        (substitute' (lift_subst_n' 1 σ) b) (substitute' σ a) (substitute' σ a')
                        (substitute' σ p)

@[simp]
def substitute_zero' (a : ATm n) (t : ATm (n + 1)) : ATm n :=
  substitute' (.extend (.weak .id) a) t

@[simp]
def zero_substitution' (a : ATm n) : ASubst n (n + 1) :=
  .extend (.weak .id) a

def n_substitution' {l n : Nat} (leq : l ≤ n) (a : ATm l) : ASubst n (n + 1) :=
  match n with
  | .zero =>
    have heq : l = Nat.zero := Iff.mp Nat.le_zero leq
    .extend (.weak .id) (heq ▸ a)
  | .succ n' =>
    if h : l < n' + 1 then
      .lift (n_substitution' (Nat.le_of_lt_succ h) a)
    else
      have heq : l = Nat.succ n' := substitute_n_helper leq h
      .extend (.weak .id) (heq ▸ a)

def n_substitution_shift' {l n : Nat} (leq : l ≤ n) (a : ATm l) : ASubst n n :=
  match n with
  | .zero =>
    .weak .id
  | .succ n' =>
    if h : l < n' + 1 then
      .lift (n_substitution_shift' (Nat.le_of_lt_succ h) a)
    else
      have heq : l = Nat.succ n' := substitute_n_helper leq h
      .extend (.weak (.shift .id)) (heq ▸ a)

prefix:96 "ₐₛ" => ASubst.weak
prefix:97 "ₐ↑ₛ" => ASubst.shift
prefix:97 "ₐ⇑ₛ" => ASubst.lift
infixl:97 "ₐₙ⇑ₛ" => lift_subst_n'
infixl:96 "⋄ₐ  " => ASubst.extend
notation:95 A "⌈ₐ" σ "⌉" => substitute' σ A
notation:95 A "⌈ₐ" σ "⌉ᵥ" => substitute_var' σ A
notation:95 A "⌈ₐ" σ "⌉₀" => substitute_zero' σ A
notation:95 a "/₀ₐ" => zero_substitution' a
notation:95 a "/ₙₐ" le => n_substitution' le a
notation:95 a "↑/ₙₐ" le => n_substitution_shift' le a
