import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import Aesop

theorem weakening_conv_var :
    v(x)⌊ρ⌋ = x⌊ρ⌋ᵥ :=
  by
    simp [weaken]

theorem weakening_var_lift {ρ ρ' : Weak m n} :
    (∀x, x⌊ρ⌋ᵥ = x⌊ρ'⌋ᵥ) → (∀x, x⌊⇑ₚρ⌋ᵥ = x⌊⇑ₚρ'⌋ᵥ) :=
  by
    intro h x
    cases x with
    | mk i _h =>
      match i with
      | 0 => rfl
      | i' + 1 =>
        simp [weaken_var]
        apply h

theorem weakening_var_lift_n {ρ ρ' : Weak m n}:
    (∀x, x⌊ρ⌋ᵥ = x⌊ρ'⌋ᵥ)
    → (∀j {x: Fin (n + j)}, x⌊j ₙ⇑ₚ ρ⌋ᵥ = x⌊j ₙ⇑ₚ ρ'⌋ᵥ) :=
  by
    intro h x n
    cases x with
    | zero =>
      simp [lift_weak_n]
      apply h
    | succ i =>
      rw [lift_weak_n]
      apply weakening_var_lift
      apply weakening_var_lift_n
      apply h

@[aesop safe apply]
theorem weakening_var_weaken :
    (∀ x, x⌊ρ⌋ᵥ = x⌊ρ'⌋ᵥ) → (∀ t, t⌊ρ⌋ = t⌊ρ'⌋) :=
  by
    intro h t
    match t with
    | .unit =>
      simp [weaken]
    | .empty =>
      simp [weaken]
    | .pi A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken
        intro i
        simp_all
    | .sigma A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken
        intro i
        simp_all
    | .nat =>
      simp [weaken]
    | .iden A a a' =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply And.intro
        · apply weakening_var_weaken h
        · apply weakening_var_weaken h
    | .univ =>
      simp [weaken]
    | .var x =>
      simp [weaken]
      apply h
    | .tt =>
      simp [weaken]
    | .indUnit A b a =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken
        apply weakening_var_lift_n
        apply h
      · apply And.intro
        · apply weakening_var_weaken h
        · apply weakening_var_weaken h
    | .indEmpty A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken
        apply weakening_var_lift_n h
      · apply weakening_var_weaken h
    | .lam A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken
        apply weakening_var_lift_n h
    | .app f a =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken h
    | .pairSigma a b =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken h
    | .indSigma A B C c p =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply And.intro
        · apply weakening_var_weaken
          apply weakening_var_lift_n h
        · apply And.intro
          · apply weakening_var_weaken
            apply weakening_var_lift_n h
          · apply And.intro
            · apply weakening_var_weaken
              apply weakening_var_lift_n h
            · apply weakening_var_weaken h
    | .zeroNat =>
      simp [weaken]
    | .succNat x =>
      simp [weaken]
      apply weakening_var_weaken h
    | .indNat A s z i =>
      simp [weaken]
      repeat' apply And.intro
      · apply weakening_var_weaken
        apply weakening_var_lift_n h
      · apply weakening_var_weaken h
      · apply weakening_var_weaken
        apply weakening_var_lift_n h
      · apply weakening_var_weaken h
    | .refl A a =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply weakening_var_weaken h
    | .j A B b a a' p =>
      simp [weaken]
      apply And.intro
      · apply weakening_var_weaken h
      · apply And.intro
        · apply weakening_var_weaken
          apply weakening_var_lift_n h
        · apply And.intro
          · apply weakening_var_weaken
            apply weakening_var_lift_n h
          · apply And.intro
            · apply weakening_var_weaken h
            · apply And.intro
              · apply weakening_var_weaken h
              · apply weakening_var_weaken h

theorem weakening_var_lift_id {n : Nat} {x : Fin (n + 1)} :
    x⌊⇑ₚidₚ⌋ᵥ = x⌊idₚ⌋ᵥ :=
  by
    match x with
    | .mk i h =>
      match i with
      | 0 => rfl
      | i' + 1 => rfl

theorem weakening_var_lift_n_id {n m : Nat} {x : Fin (n + m)} :
    x⌊m ₙ⇑ₚidₚ⌋ᵥ = x⌊idₚ⌋ᵥ :=
  by
    match m with
    | 0 => rfl
    | m' + 1 =>
      match x with
      | .mk i h =>
        match i with
        | 0 => rfl
        | i' + 1 =>
          rw [lift_weak_n]
          simp [weaken_var]
          rw [weakening_var_lift_n_id]
          rfl

@[simp]
theorem weakening_id :
    ∀ {t : Tm n}, t⌊idₚ⌋ = t :=
  by
    intro t
    match t with
    | .unit =>
      simp [weaken]
    | .empty =>
      simp [weaken]
    | .pi A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · have h := weakening_id (t := B)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        simp_all
        aesop
    | .sigma A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · have h := weakening_id (t := B)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        simp_all
        aesop
    | .nat =>
      simp [weaken]
    | .iden A a a' =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply And.intro
        · apply weakening_id
        · apply weakening_id
    | .univ =>
      simp [weaken]
    | .var x =>
      simp [weaken]
    | .tt =>
      simp [weaken]
    | .indUnit A b a =>
      simp [weaken]
      apply And.intro
      · have h := weakening_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        simp_all
        aesop
      · apply And.intro
        · apply weakening_id
        · apply weakening_id
    | .indEmpty A b =>
      simp [weaken]
      apply And.intro
      · have h := weakening_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        simp_all
        aesop
      · apply weakening_id
    | .lam A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · have h := weakening_id (t := b)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        simp_all
        aesop
    | .app f a =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply weakening_id
    | .pairSigma a b =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply weakening_id
    | .indSigma A B C c p =>
      simp [-lift_weak_n]
      apply And.intro
      · apply weakening_id
      · apply And.intro
        · have h := weakening_id (t := B)
          rw (config := {occs := .pos [2]}) [←h]
          apply weakening_var_weaken
          intro i
          apply weakening_var_lift_id
        · apply And.intro
          · have h := weakening_id (t := C)
            rw (config := {occs := .pos [2]}) [←h]
            apply weakening_var_weaken
            apply weakening_var_lift_id
          · apply And.intro
            · have h := weakening_id (t := c)
              rw (config := {occs := .pos [2]}) [←h]
              apply weakening_var_weaken
              intro i
              apply weakening_var_lift_n_id
            · apply weakening_id
    | .zeroNat =>
      simp [weaken]
    | .succNat x =>
      simp [weaken]
      apply weakening_id
    | .indNat A z s i =>
      simp [-lift_weak_n]
      repeat' apply And.intro
      · have h := weakening_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        simp_all
        aesop
      · apply weakening_id
      · have h := weakening_id (t := s)
        rw (config := {occs := .pos [2]}) [←h]
        apply weakening_var_weaken
        intro i
        apply weakening_var_lift_n_id
      · apply weakening_id
    | .refl A a =>
      simp [weaken]
      apply And.intro
      · apply weakening_id
      · apply weakening_id
    | .j A B b a a' p =>
      simp [-lift_weak_n]
      apply And.intro
      · apply weakening_id
      · apply And.intro
        · have h := weakening_id (t := B)
          rw (config := {occs := .pos [2]}) [←h]
          apply weakening_var_weaken
          intro i
          apply weakening_var_lift_n_id
        · apply And.intro
          · have h := weakening_id (t := b)
            rw (config := {occs := .pos [2]}) [←h]
            apply weakening_var_weaken
            intro i
            simp_all
            aesop
          · apply And.intro
            · apply weakening_id
            · apply And.intro
              · apply weakening_id
              · apply weakening_id

@[simp]
theorem weakening_lift_id {t : Tm (n + 1)} :
    t⌊⇑ₚidₚ⌋ = t :=
  by
    have h :=  weakening_id (t := t)
    rw (config := {occs := .pos [2]}) [←h]
    apply weakening_var_weaken
    intro i
    apply weakening_var_lift_id

theorem weakening_univ {ρ : Weak m n} :
    𝒰⌊ρ⌋ = 𝒰 :=
  by
    simp [weaken]

theorem weakening_unit {ρ : Weak m n} :
    𝟙⌊ρ⌋ = 𝟙 :=
  by
    simp [weaken]

theorem weakening_tt {ρ : Weak m n} :
    ⋆⌊ρ⌋ = ⋆  :=
  by
    simp [weaken]

theorem weakening_empty {ρ : Weak m n} :
    𝟘⌊ρ⌋ = 𝟘 :=
  by
    simp [weaken]

theorem weakening_pi {ρ : Weak m n} :
    (ΠA;B)⌊ρ⌋ = Π(A⌊ρ⌋);(B⌊⇑ₚρ⌋) :=
  by
    simp []

theorem weakening_sigma {ρ : Weak m n} :
    (ΣA;B)⌊ρ⌋ = Σ(A⌊ρ⌋);(B⌊⇑ₚρ⌋) :=
  by
    simp [weaken]

theorem weakening_nat {ρ : Weak m n} :
    𝒩 ⌊ρ⌋ = 𝒩 :=
  by
    simp [weaken]

theorem weakening_iden {ρ : Weak m n} :
    (.iden A a a')⌊ρ⌋ = .iden (A⌊ρ⌋) (a⌊ρ⌋) (a'⌊ρ⌋) :=
  by
    simp [weaken]

theorem weakening_refl {ρ : Weak m n} :
    (.refl A a)⌊ρ⌋ = .refl (A⌊ρ⌋) (a⌊ρ⌋) :=
  by
    simp [weaken]

theorem weakening_nat_zero {ρ : Weak m n} :
    𝓏⌊ρ⌋ = 𝓏 :=
  by
    simp [weaken]

theorem weaken_from_zero {geq : l ≥ n} :
    weaken_from n l = ↑ₚidₚ :=
  by
    cases n with
    | zero =>
      rw [weaken_from]
    | succ n' =>
      rw [weaken_from]
      split
      case succ.isTrue hT =>
        omega
      case succ.isFalse hF =>
        rfl

theorem lift_weaken_from {n : Nat} {leq : l ≤ n} :
    ⇑ₚweaken_from n l = weaken_from (n + 1) l :=
  by
    simp [weaken_from]
    omega

@[simp]
theorem lift_weaken_from_simp {n : Nat} {leq : l ≤ n} :
     weaken_from (n + 1) l = ⇑ₚweaken_from n l :=
  by
    simp [weaken_from]
    omega

theorem weakening_shift_vone {n : Nat} :
    (v(1)) = (v(0) : Tm (n + 1))⌊↑ₚidₚ⌋ :=
  by
    simp []

theorem weakening_shift_var {n : Nat} {x : Fin n} :
    (v(x.succ) : Tm (n + 1)) = v(x)⌊↑ₚidₚ⌋ :=
  by
    simp []

theorem weakening_var_weaken_id :
    (∀ (x : Fin n), x⌊ρ⌋ᵥ = x) → ∀ (t : Tm n), t⌊ρ⌋ = t :=
  by
    intro h t
    rw (config := {occs := .pos [2]}) [←weakening_id (t := t)]
    apply weakening_var_weaken
    intro x
    apply h
