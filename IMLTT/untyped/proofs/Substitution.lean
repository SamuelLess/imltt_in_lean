import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

import Aesop

theorem substitution_var_lift {σ σ' : Subst m n} :
    (∀ (x : Fin n), v(x)⌈σ⌉ = v(x)⌈σ'⌉) → ∀ (x : Fin (n + 1)), v(x)⌈⇑ₛσ⌉ = v(x)⌈⇑ₛσ'⌉ :=
  by
    aesop

theorem substitution_var_lift_n {σ σ' : Subst m n} :
    (∀ (x : Fin n), v(x)⌈σ⌉ = v(x)⌈σ'⌉) → ∀ (x : Fin (n + l)), v(x)⌈l ₙ⇑ₛσ⌉ = v(x)⌈l ₙ⇑ₛσ'⌉ :=
  by
    intro h x
    cases l with
    | zero =>
      simp_all
    | succ i' =>
      rw [lift_subst_n]
      apply substitution_var_lift
      apply substitution_var_lift_n
      apply h

@[aesop safe apply]
theorem substitution_var_substitute {σ σ' : Subst m n} :
    (∀ (x : Fin n), v(x)⌈σ⌉ = v(x)⌈σ'⌉) → ∀ (t : Tm n), t⌈σ⌉ = t⌈σ'⌉ :=
  by
    intro h t
    match t with
    | .unit =>
      simp []
    | .empty =>
      simp []
    | .pi A B =>
      simp []
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute
        apply substitution_var_lift_n h
    | .sigma A B =>
      simp []
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute
        apply substitution_var_lift_n h
    | .nat =>
      simp []
    | .iden A a a' =>
      simp []
      apply And.intro
      · apply substitution_var_substitute h
      · apply And.intro
        · apply substitution_var_substitute h
        · apply substitution_var_substitute h
    | .univ =>
      simp []
    | .var x =>
      apply h
    | .tt =>
      simp []
    | .indUnit A b a =>
      simp []
      apply And.intro
      · apply substitution_var_substitute
        apply substitution_var_lift h
      · apply And.intro
        · apply substitution_var_substitute h
        · apply substitution_var_substitute h
    | .indEmpty A b =>
      simp []
      apply And.intro
      · apply substitution_var_substitute
        apply substitution_var_lift h
      · apply substitution_var_substitute h
    | .lam A b =>
      simp []
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute
        apply substitution_var_lift h
    | .app f a =>
      simp []
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute h
    | .pairSigma a b =>
      simp []
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute h
    | .indSigma A B C c p =>
      simp []
      apply And.intro
      · apply substitution_var_substitute h
      · apply And.intro
        · apply substitution_var_substitute
          apply substitution_var_lift h
        · apply And.intro
          · apply substitution_var_substitute
            apply substitution_var_lift h
          · apply And.intro
            · apply substitution_var_substitute
              apply substitution_var_lift_n h
            · apply substitution_var_substitute h
    | .zeroNat =>
      simp [substitute]
    | .succNat x =>
      simp [substitute]
      apply substitution_var_substitute h
    | .indNat A z s i =>
      simp [substitute]
      repeat' apply And.intro
      · apply substitution_var_substitute
        apply substitution_var_lift_n h
      · apply substitution_var_substitute h
      · apply substitution_var_substitute
        apply substitution_var_lift_n h
      · apply substitution_var_substitute h
    | .refl A a =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply substitution_var_substitute h
    | .j A B b a a' p =>
      simp [substitute]
      apply And.intro
      · apply substitution_var_substitute h
      · apply And.intro
        · apply substitution_var_substitute
          apply substitution_var_lift_n h
        · apply And.intro
          · apply substitution_var_substitute
            apply substitution_var_lift_n h
          · apply And.intro
            · apply substitution_var_substitute h
            · apply And.intro
              · apply substitution_var_substitute h
              · apply substitution_var_substitute h

theorem substitution_var_lift_id {x : Fin (n + 1)} :
    v(x)⌈⇑ₛ(ₛidₚ)⌉ = v(x)⌈ₛidₚ⌉ :=
  by
    match x with
    | .mk i h =>
      match i with
      | 0 => rfl
      | i' + 1 => rfl

theorem substitution_var_lift_n_id {n m : Nat} {x : Fin (n + m)} :
    v(x)⌈m ₙ⇑ₛ(ₛidₚ)⌉ = v(x)⌈ₛidₚ⌉ :=
  by
    match m with
    | 0 => rfl
    | m' + 1 =>
      match x with
      | .mk i h =>
        match i with
        | 0 => rfl
        | i' + 1 =>
          have h := substitution_var_lift_n_id (n := n) (x := .mk i' (Nat.lt_of_succ_lt_succ h))
          simp_all

@[simp]
theorem substitution_id {t : Tm n} :
    t⌈ₛidₚ⌉ = t :=
  by
    match t with
    | .unit =>
      simp [substitute]
    | .empty =>
      simp [substitute]
    | .pi A B =>
      simp [-lift_subst_n]
      apply And.intro
      · apply substitution_id
      · have h := substitution_id (t := B)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
    | .sigma A B =>
      simp [-lift_subst_n]
      apply And.intro
      · apply substitution_id
      · have h := substitution_id (t := B)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
    | .nat =>
      simp [substitute]
    | .iden A a a' =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply And.intro
        · apply substitution_id
        · apply substitution_id
    | .univ =>
      simp [substitute]
    | .var x =>
      simp [substitute]
    | .tt =>
      simp [substitute]
    | .indUnit A b a =>
      simp [-lift_subst_n]
      apply And.intro
      · have h := substitution_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
      · apply And.intro
        · apply substitution_id
        · apply substitution_id
    | .indEmpty A b =>
      simp [-lift_subst_n]
      apply And.intro
      · have h := substitution_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
      · apply substitution_id
    | .lam A b =>
      simp [-lift_subst_n]
      apply And.intro
      · apply substitution_id
      · have h := substitution_id (t := b)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
    | .app f a =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply substitution_id
    | .pairSigma a b =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply substitution_id
    | .indSigma A B C c p =>
      simp [-lift_subst_n]
      apply And.intro
      · apply substitution_id
      · apply And.intro
        · have h := substitution_id (t := B)
          rw (config := {occs := .pos [2]}) [←h]
          apply substitution_var_substitute
          intro x
          apply substitution_var_lift_n_id
        · apply And.intro
          · have h := substitution_id (t := C)
            rw (config := {occs := .pos [2]}) [←h]
            apply substitution_var_substitute
            intro x
            apply substitution_var_lift_n_id
          · apply And.intro
            · have h := substitution_id (t := c)
              rw (config := {occs := .pos [2]}) [←h]
              apply substitution_var_substitute
              intro x
              apply substitution_var_lift_n_id
            · apply substitution_id
    | .zeroNat =>
      simp [substitute]
    | .succNat i =>
      simp [substitute]
      apply substitution_id
    | .indNat A z s i =>
      simp [-lift_subst_n]
      repeat' apply And.intro
      · have h := substitution_id (t := A)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
      · apply substitution_id
      · have h := substitution_id (t := s)
        rw (config := {occs := .pos [2]}) [←h]
        apply substitution_var_substitute
        intro x
        apply substitution_var_lift_n_id
      · apply substitution_id
    | .refl A a =>
      simp [substitute]
      apply And.intro
      · apply substitution_id
      · apply substitution_id
    | .j A B b a a' p =>
      simp [-lift_subst_n]
      apply And.intro
      · apply substitution_id
      · apply And.intro
        · have h := substitution_id (t := B)
          rw (config := {occs := .pos [2]}) [←h]
          apply substitution_var_substitute
          intro x
          apply substitution_var_lift_n_id
        · apply And.intro
          · have h := substitution_id (t := b)
            rw (config := {occs := .pos [2]}) [←h]
            apply substitution_var_substitute
            intro x
            apply substitution_var_lift_n_id
          · apply And.intro
            · apply substitution_id
            · apply And.intro
              · apply substitution_id
              · apply substitution_id


theorem substitution_conv_lift_id :
    ∀ (x : Fin (n + 1)), v(x)⌈ₛ⇑ₚidₚ⌉ = v(x)⌈⇑ₛ(ₛidₚ)⌉ :=
  by
    intro x
    simp [substitute]
    cases x with
    | mk i h =>
      cases i with
      | zero =>
        rfl
      | succ i' =>
        rfl

@[simp]
theorem substitution_lift_id {t : Tm (n + 1)} :
    t⌈ₛ⇑ₚidₚ⌉ = t :=
  by
    have h := substitution_id (t := t)
    rw (config := {occs := .pos [2]}) [←h]
    apply substitution_var_substitute
    intro i
    rw [←substitution_var_lift_id]
    apply substitution_conv_lift_id

theorem substitution_univ : 𝒰⌈σ⌉ = 𝒰 :=
  by
    simp [substitute]

theorem substitution_unit : 𝟙⌈σ⌉ = 𝟙 :=
  by
    simp [substitute]

theorem substitution_empty : 𝟘⌈σ⌉ = 𝟘 :=
  by
    simp [substitute]

theorem substitution_tt : ⋆⌈σ⌉ = ⋆ :=
  by
    simp [substitute]

theorem substitution_pi : (ΠA;B)⌈σ⌉ = ΠA⌈σ⌉;B⌈⇑ₛσ⌉ :=
  by
    simp [substitute]

theorem substitution_lambda : (λA;b)⌈σ⌉ = λA⌈σ⌉;b⌈⇑ₛσ⌉ :=
  by
    simp [substitute]

theorem substitution_sigma : (ΣA;B)⌈σ⌉ = ΣA⌈σ⌉;B⌈⇑ₛσ⌉ :=
  by
    simp [substitute]

theorem substitution_pair : (a&b)⌈σ⌉ = (a⌈σ⌉)&(b⌈σ⌉) :=
  by
    simp [substitute]

theorem substitution_nat : 𝒩 ⌈σ⌉ = 𝒩  :=
  by
    simp [substitute]

theorem substitution_iden : (a ≃[A] a')⌈σ⌉ = a⌈σ⌉ ≃[A⌈σ⌉] a'⌈σ⌉ :=
  by
    simp [substitute]

theorem substitution_var_zero : 𝓏⌈σ⌉ = 𝓏 :=
  by
    simp [substitute]

theorem substitution_succ : 𝓈(x)⌈σ⌉ = 𝓈(x⌈σ⌉) :=
  by
    simp [substitute]

theorem substitution_refl : (.refl A a)⌈σ⌉ = .refl (A⌈σ⌉) (a⌈σ⌉) :=
  by
    simp [substitute]

theorem lift_n_substitution {n : Nat} {leq : l ≤ n} {s : Tm l} :
    ⇑ₛ(s/ₙleq) = s/ₙ(Nat.le_succ_of_le leq) :=
  by
    simp [n_substitution]
    omega

@[simp]
theorem n_substitution_zero {n : Nat} {s : Tm n}:
    (s/ₙ (Nat.le_refl n)) = s/₀ :=
  by
    simp [zero_substitution]
    cases n with
    | zero =>
      simp [n_substitution]
    | succ n' =>
      simp [n_substitution]

theorem substitution_unit_sub :
    ¬(∀ {n : Nat} {B : Tm (n + 1)} {a : Tm n}, 𝟙 = B⌈a⌉₀ → B = 𝟙) :=
  by
    intro hEq
    have h : (𝟙 : Tm 0) = v(0)⌈𝟙⌉₀ :=
        by simp []
    have h1 := hEq h
    cases h1

@[simp]
theorem substitution_id_shift_var :
    A⌈(ₛ(↑ₚidₚ))⋄ v(0)⌉ = A :=
  by
    rw (config := {occs := .pos [2]}) [←substitution_id (t := A)]
    apply substitution_var_substitute
    aesop

theorem lift_n_substitution_shift {n : Nat} {leq : l ≤ n} {s : Tm l} :
    ⇑ₛ(s↑/ₙleq) = s↑/ₙ(Nat.le_succ_of_le leq) :=
  by
    simp [n_substitution_shift]
    omega

@[simp]
theorem n_substitution_shift_zero {n : Nat} {s : Tm (n + 1)} :
    (s↑/ₙ(Nat.le_refl (n + 1))) = (ₛ↑ₚidₚ)⋄ s :=
  by
    simp [n_substitution_shift]

theorem substitution_var_substitute_id :
    (∀ (x : Fin n), x⌈σ⌉ᵥ = x) → ∀ (t : Tm n), t⌈σ⌉ = t :=
  by
    intro h t
    rw (config := {occs := .pos [2]}) [←substitution_id (t := t)]
    apply substitution_var_substitute
    intro x
    rw [substitution_id]
    apply h
