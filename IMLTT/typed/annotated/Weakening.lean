import IMLTT.typed.annotated.Syntax
import IMLTT.untyped.Weakening

@[simp]
def weaken' (ρ : Weak m n) (t : ATm n) : ATm m :=
  match t with
  | .unit => .unit
  | .empty => .empty
  | .pi A B => .pi (weaken' ρ A) (weaken' (lift_weak_n 1 ρ) B)
  | .sigma A B => .sigma (weaken' ρ A) (weaken' (lift_weak_n 1 ρ) B)
  | .nat => .nat
  | .iden A a a' => .iden (weaken' ρ A) (weaken' ρ a) (weaken' ρ a')
  | .univ => .univ
  | .var i => .var <| weaken_var ρ i
  | .tt => .tt
  | .indUnit A b a => .indUnit (weaken' (lift_weak_n 1 ρ) A) (weaken' ρ b) (weaken' ρ a)
  | .indEmpty A b => .indEmpty (weaken' (lift_weak_n 1 ρ) A) (weaken' ρ b)
  | .lam A b => .lam (weaken' ρ A) (weaken' (lift_weak_n 1 ρ) b)
  | .app f a => .app (weaken' ρ f) (weaken' ρ a)
  | .pairSigma a b S => .pairSigma (weaken' ρ a) (weaken' ρ b) (weaken' (lift_weak_n 1 ρ) S)
  | .indSigma A B C c p => .indSigma (weaken' ρ A) (weaken' (lift_weak_n 1 ρ) B)
                            (weaken' (lift_weak_n 1 ρ) C) (weaken' (lift_weak_n 2 ρ) c) (weaken' ρ p)
  | .zeroNat => .zeroNat
  | .succNat a => .succNat (weaken' ρ a)
  | .indNat A s z n => .indNat (weaken' (lift_weak_n 1 ρ) A) (weaken' ρ s) (weaken' (lift_weak_n 2 ρ) z)
                        (weaken' ρ n)
  | .refl A a => .refl (weaken' ρ A) (weaken' ρ a)
  | .j A B b a a' p => .j (weaken' ρ A) (weaken' (lift_weak_n 3 ρ) B) (weaken' (lift_weak_n 1 ρ) b)
                        (weaken' ρ a) (weaken' ρ a') (weaken' ρ p)

@[simp]
def shift_tm' : ATm n → ATm (n + 1)
  | t => weaken' (.shift .id) t

notation:95 A "⌊ₐ" ρ "⌋" => weaken' ρ A

theorem toTm_weak {m n : Nat} (ρ : Weak m n) (t : ATm n) :
    ATm.toTm (t⌊ₐρ⌋) = t.toTm⌊ρ⌋ := by
  induction t generalizing m <;> simp [weaken', ATm.toTm, *]
