import IMLTT.untyped.AbstractSyntax

inductive Weak : Nat → Nat → Type where
  | id : Weak n n
  | shift : Weak m n → Weak (m + 1) n
  | lift : Weak m n → Weak (m + 1) (n + 1)

@[simp]
def lift_weak_n (i : Nat) (ρ : Weak m n) : Weak (m + i) (n + i) :=
  match i with
  | 0 => ρ
  | i' + 1 => .lift (lift_weak_n i' ρ)

@[simp]
def weaken_var (ρ : Weak m n) (x : Fin n) : Fin m :=
  match ρ with
  | .id => x
  | .shift ρ => .succ (weaken_var ρ x)
  | .lift ρ =>
    match x with
    | ⟨0, _⟩ => 0
    | ⟨x' + 1, h⟩ => .succ (weaken_var ρ (Fin.mk x' (Nat.lt_of_succ_lt_succ h)))

@[simp]
def weaken (ρ : Weak m n) (t : Tm n) : Tm m :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (weaken ρ A) (weaken (lift_weak_n 1 ρ) B)
  | .sigma A B => .sigma (weaken ρ A) (weaken (lift_weak_n 1 ρ) B)
  | .nat => .nat
  | .iden A a a' => .iden (weaken ρ A) (weaken ρ a) (weaken ρ a')
  | .univ => .univ
  | .var i => weaken_var ρ i
  | .tt => .tt
  | .indUnit A b a => .indUnit (weaken (lift_weak_n 1 ρ) A) (weaken ρ b) (weaken ρ a)
  | .indEmpty A b => .indEmpty (weaken (lift_weak_n 1 ρ) A) (weaken ρ b)
  | .lam A b => .lam (weaken ρ A) (weaken (lift_weak_n 1 ρ) b)
  | .app f a => .app (weaken ρ f) (weaken ρ a)
  | .pairSigma a b => .pairSigma (weaken ρ a) (weaken ρ b)
  | .indSigma A B C c p => .indSigma (weaken ρ A) (weaken (lift_weak_n 1 ρ) B)
                            (weaken (lift_weak_n 1 ρ) C) (weaken (lift_weak_n 2 ρ) c) (weaken ρ p)
  | .zeroNat => .zeroNat
  | .succNat a => .succNat (weaken ρ a)
  | .indNat A s z n => .indNat (weaken (lift_weak_n 1 ρ) A) (weaken ρ s) (weaken (lift_weak_n 2 ρ) z)
                        (weaken ρ n)
  | .refl A a => .refl (weaken ρ A) (weaken ρ a)
  | .j A B b a a' p => .j (weaken ρ A) (weaken (lift_weak_n 3 ρ) B) (weaken (lift_weak_n 1 ρ) b)
                        (weaken ρ a) (weaken ρ a') (weaken ρ p)

@[simp]
def shift_tm : Tm n → Tm (n + 1)
  | t => weaken (.shift .id) t

def weaken_from (n : Nat) (l : Nat) : Weak (n + 1) n :=
  match n with
  | .zero => .shift .id
  | .succ n' =>
    if l < n' + 1 then
      .lift (weaken_from n' l)
    else
      .shift .id

notation:max "idₚ" => Weak.id
prefix:97 "↑ₚ" => Weak.shift
prefix:97 "⇑ₚ" => Weak.lift
infixl:97 "ₙ⇑ₚ" => lift_weak_n
notation:97 "↑₁" n "↬" l => weaken_from n l
notation:95 v "⌊" ρ "⌋ᵥ" => weaken_var ρ v
notation:95 A "⌊" ρ "⌋" => weaken ρ A
