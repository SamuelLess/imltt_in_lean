import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Contexts
import IMLTT.untyped.proofs.Contexts

import IMLTT.typed.JudgmentsAndRules

theorem defeq_refl_var :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type
    → ((∀ (eqM : x = 0) (A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → (∀ (eqM : x + 1 = 0) (a A_1 : Tm 0),
        eqM ▸ Γ ⬝ A = ε
        → eqM ▸ v(0) = a
        → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ v(0) = a
        → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n Γ A hA ihA
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases Δ with
      | start =>
        cases heqΓ
        rw [←empty_expand_context (Γ := Γ)]
        cases Γ with
        | empty =>
          apply And.left ihA
          repeat' rfl
        | extend Γ' S' =>
          apply And.right (And.right ihA)
          repeat' rfl
      | expand Δ' S' =>
        cases heqΓ
        apply And.left (And.right ihA)
        rotate_left
        · apply n
        · apply Δ'
        repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqt
      cases heqT
      cases Δ with
      | start =>
        cases heqΓ
        apply IsEqualTerm.var_eq hA
      | expand Δ' S' =>
        cases heqΓ
        apply IsEqualTerm.var_eq hA

theorem defeq_refl_weak :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ∶ A)
    → Γ ⊢ B type
    → ((∀ (eqM : x = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ v(i) = a
        → eqM ▸ A = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ v(i) = a
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : x = 0) (A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ B = A
        → ε ⊢ A ≡ A type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (A : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ B = A
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A ≡ A type)
    → (∀ (eqM : x + 1 = 0) (a A_1 : Tm 0),
        eqM ▸ Γ ⬝ B = ε
        → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a
        → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ
        → Γ_1 ⊢ B_1 ≡ B_1 type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a
        → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n x Γ A B hvA hB ihvA ihB
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases Δ with
      | start =>
        cases heqΓ
        rw [←empty_expand_context (Γ := Γ)]
        cases Γ with
        | empty =>
          apply And.left ihB
          repeat' rfl
        | extend Γ' S' =>
          apply And.right (And.right ihB)
          repeat' rfl
      | expand Δ' S' =>
        cases heqΓ
        apply And.left (And.right ihB)
        rotate_left
        · apply n
        · apply Δ'
        repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqt
      cases heqT
      cases Δ with
      | start =>
        cases heqΓ
        apply IsEqualTerm.weak_eq
        · cases Γ with
          | empty =>
            apply And.left ihvA
            repeat' rfl
          | extend Γ' S' =>
            rw [←empty_expand_context (Γ := Γ' ⬝ S')]
            apply And.right (And.right ihvA)
            repeat' rfl
        · apply hB
      | expand Δ' S' =>
        cases heqΓ
        apply IsEqualTerm.weak_eq
        · apply And.right (And.right ihvA)
          repeat' rfl
        · apply hB

theorem defeq_refl_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (a A : Tm 0), eqM ▸ Γ = ε → eqM ▸ ⋆ = a → eqM ▸ 𝟙 = A → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ ⋆ = a
        → eqM ▸ 𝟙 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.unit_intro_eq
      apply hiC
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      cases Δ
      case start =>
        apply ihiC
        rotate_left
        · apply m + 1
        · apply CtxGen.start
        · rfl
        · rfl
      case expand n' Δ' S =>
        apply ihiC
        rotate_left
        · apply n' + 1
        · apply Δ' ⊙ S
        · rfl
        · rfl
    · intro  m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.unit_intro_eq
      apply hiC

theorem defeq_refl_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ∶ B)
    → ((∀ (eqM : n + 1 = 0) (a A_1 : Tm 0),
        eqM ▸ Γ ⬝ A = ε
        → eqM ▸ b = a
        → eqM ▸ B = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
          eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
          → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
          eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ
          → eqM ▸ b = a
          → eqM ▸ B = A_1
          → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → (∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → (eqM ▸ λA; b) = a
        → (eqM ▸ ΠA;B) = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → (eqM ▸ λA; b) = a
        → (eqM ▸ ΠA;B) = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n Γ A b B hbB ihbB
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.pi_intro_eq
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply And.right (And.right ihbB)
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε)]
        apply And.left (And.right ihbB)
        rotate_left
        · apply 1
        · apply CtxGen.start
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihbB)
      rotate_left
      · apply n + 1
      · apply Δ ⊙ A
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.pi_intro_eq
      · rw [extend_expand_context]
        apply And.right (And.right ihbB)
        repeat' rfl
      · apply And.left (And.right ihbB)
        rotate_left
        · apply n + 1
        · apply CtxGen.start
        repeat' rfl

theorem defeq_refl_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ∶ A)
    → (Γ ⊢ b ∶ B⌈a⌉₀)
    → Γ ⬝ A ⊢ B type
    → ((∀ (eqM : n = 0) (a_4 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a = a_4
        → eqM ▸ A = A_1
        → ε ⊢ a_4 ≡ a_4 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_4 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a = a_4
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_4 ≡ a_4 ∶ A_1)
    → ((∀ (eqM : n = 0) (a_5 A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ b = a_5
        → eqM ▸ B⌈a⌉₀ = A
        → ε ⊢ a_5 ≡ a_5 ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ b = a_5
        → eqM ▸ B⌈a⌉₀ = A
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A)
    → ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0),
        eqM ▸ Γ ⬝ A = ε
        → eqM ▸ B = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ B = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → (∀ (eqM : n = 0) (a_7 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a&b = a_7
        → (eqM ▸ ΣA;B) = A_1
        → ε ⊢ a_7 ≡ a_7 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_7 A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ a&b = a_7
        → (eqM ▸ ΣA;B) = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_7 ≡ a_7 ∶ A_1 :=
  by
    intro n Γ' a A b B haA hbB hA ihaA ihbB ihA
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.sigma_intro_eq
      · apply And.left ihaA
        repeat' rfl
      · apply And.left ihbB
        repeat' rfl
      · apply hA
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihbB)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.sigma_intro_eq
      · apply And.right (And.right ihaA)
        repeat' rfl
      · apply And.right (And.right ihbB)
        repeat' rfl
      · apply hA

theorem defeq_refl_nat_zero_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (a A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝓏 = a → eqM ▸ 𝒩 = A → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝓏 = a
        → eqM ▸ 𝒩 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.nat_zero_intro_eq
      apply hiC
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      cases Δ
      case start =>
        apply ihiC
        rotate_left
        · apply m + 1
        · apply CtxGen.start
        · rfl
        · rfl
      case expand n' Δ' S =>
        apply ihiC
        rotate_left
        · apply n' + 1
        · apply Δ' ⊙ S
        · rfl
        · rfl
    · intro  m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.nat_zero_intro_eq
      apply hiC

theorem defeq_refl_nat_succ_intro :
    ∀ {n : Nat} {Γ : Ctx n} {x : Tm n},
    (Γ ⊢ x ∶ 𝒩)
    → ((∀ (eqM : n = 0) (a A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ x = a
        → eqM ▸ 𝒩 = A
        → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ x = a
        → eqM ▸ 𝒩 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A)
    → (∀ (eqM : n = 0) (a A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ 𝓈(x) = a
        → eqM ▸ 𝒩 = A
        → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝓈(x) = a
        → eqM ▸ 𝒩 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A :=
  by
    intro n Γ x hxNat ihxNat
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.nat_succ_intro_eq
      apply And.left ihxNat
      repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihxNat)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.nat_succ_intro_eq
      apply And.right (And.right ihxNat)
      repeat' rfl

theorem defeq_refl_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
    Γ ⊢ A type
    → (Γ ⊢ a ∶ A)
    → ((∀ (eqM : n = 0) (A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → ((∀ (eqM : n = 0) (a_4 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a = a_4
        → eqM ▸ A = A_1
        → ε ⊢ a_4 ≡ a_4 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_4 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a = a_4
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_4 ≡ a_4 ∶ A_1)
    → (∀ (eqM : n = 0) (a_5 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A.refl a = a_5
        → (eqM ▸ a ≃[A] a) = A_1
        → ε ⊢ a_5 ≡ a_5 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A.refl a = a_5
        → (eqM ▸ a ≃[A] a) = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A_1 :=
  by
    intro n Γ A a hA haA ihA ihaA
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.iden_intro_eq
      · apply And.left ihA
        repeat' rfl
      · apply And.left ihaA
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihA)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.iden_intro_eq
      · apply And.right (And.right ihA)
        repeat' rfl
      · apply And.right (And.right ihaA)
        repeat' rfl

theorem defeq_refl_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (a A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ 𝟙 = a
        → eqM ▸ 𝒰 = A
        → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝟙 = a
        → eqM ▸ 𝒰 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_unit_eq
      apply hiC
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      cases Δ
      case start =>
        apply ihiC
        rotate_left
        · apply m + 1
        · apply CtxGen.start
        · rfl
        · rfl
      case expand n' Δ' S =>
        apply ihiC
        rotate_left
        · apply n' + 1
        · apply Δ' ⊙ S
        · rfl
        · rfl
    · intro  m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_unit_eq
      apply hiC

theorem defeq_refl_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (a A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ 𝟘 = a
        → eqM ▸ 𝒰 = A
        → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝟘 = a
        → eqM ▸ 𝒰 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_empty_eq
      apply hiC
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      cases Δ
      case start =>
        apply ihiC
        rotate_left
        · apply m + 1
        · apply CtxGen.start
        · rfl
        · rfl
      case expand n' Δ' S =>
        apply ihiC
        rotate_left
        · apply n' + 1
        · apply Δ' ⊙ S
        · rfl
        · rfl
    · intro  m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_empty_eq
      apply hiC

theorem defeq_refl_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ∶ 𝒰)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A = a
        → eqM ▸ 𝒰 = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = a
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n + 1 = 0) (a A_1 : Tm 0),
        eqM ▸ Γ ⬝ A = ε
        → eqM ▸ B = a
        → eqM ▸ 𝒰 = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ B = a
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → (∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → (eqM ▸ ΠA;B) = a
        → eqM ▸ 𝒰 = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → (eqM ▸ ΠA;B) = a
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n Γ A B hA hB ihAU ihBU
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_pi_eq
      · apply And.left ihAU
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply And.right (And.right ihBU)
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihAU)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_pi_eq
      · apply And.right (And.right ihAU)
        repeat' rfl
      · rw [extend_expand_context]
        apply And.right (And.right ihBU)
        repeat' rfl

theorem defeq_refl_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ∶ 𝒰)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A = a
        → eqM ▸ 𝒰 = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = a
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n + 1 = 0) (a A_1 : Tm 0),
        eqM ▸ Γ ⬝ A = ε
        → eqM ▸ B = a
        → eqM ▸ 𝒰 = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ B = a
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → (∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → (eqM ▸ ΣA;B) = a
        → eqM ▸ 𝒰 = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → (eqM ▸ ΣA;B) = a
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n Γ A B hA hB ihAU ihBU
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_sigma_eq
      · apply And.left ihAU
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply And.right (And.right ihBU)
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihAU)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_sigma_eq
      · apply And.right (And.right ihAU)
        repeat' rfl
      · rw [extend_expand_context]
        apply And.right (And.right ihBU)
        repeat' rfl

theorem defeq_refl_univ_nat :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (a A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ 𝒩 = a
        → eqM ▸ 𝒰 = A
        → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝒩 = a
        → eqM ▸ 𝒰 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_nat_eq
      apply hiC
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      cases Δ
      case start =>
        apply ihiC
        rotate_left
        · apply m + 1
        · apply CtxGen.start
        · rfl
        · rfl
      case expand n' Δ' S =>
        apply ihiC
        rotate_left
        · apply n' + 1
        · apply Δ' ⊙ S
        · rfl
        · rfl
    · intro  m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_nat_eq
      apply hiC

theorem defeq_refl_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A = a
        → eqM ▸ 𝒰 = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = a
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n = 0) (a_5 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a = a_5
        → eqM ▸ A = A_1
        → ε ⊢ a_5 ≡ a_5 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a = a_5
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A_1)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a' = a
        → eqM ▸ A = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a' = a
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → (∀ (eqM : n = 0) (a_7 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → (eqM ▸ a ≃[A] a') = a_7
        → eqM ▸ 𝒰 = A_1
        → ε ⊢ a_7 ≡ a_7 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_7 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → (eqM ▸ a ≃[A] a') = a_7
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_7 ≡ a_7 ∶ A_1 :=
  by
    intro n Γ' A a a' hAU haA haA' ihAU ihaA ihaA'
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_iden_eq
      · apply And.left ihAU
        repeat' rfl
      · apply And.left ihaA
        repeat' rfl
      · apply And.left ihaA'
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihAU)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_iden_eq
      · apply And.right (And.right ihAU)
        repeat' rfl
      · apply And.right (And.right ihaA)
        repeat' rfl
      · apply And.right (And.right ihaA')
        repeat' rfl

theorem defeq_refl_unit_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type
    → (Γ ⊢ a ∶ A⌈⋆⌉₀)
    → (Γ ⊢ b ∶ 𝟙)
    → ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0),
        eqM ▸ Γ ⬝ 𝟙 = ε
        → eqM ▸ A = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → ((∀ (eqM : n = 0) (a_5 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a = a_5
        → eqM ▸ A⌈⋆⌉₀ = A_1
        → ε ⊢ a_5 ≡ a_5 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a = a_5
        → eqM ▸ A⌈⋆⌉₀ = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A_1)
    → ((∀ (eqM : n = 0) (a A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ b = a
        → eqM ▸ 𝟙 = A
        → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ b = a
        → eqM ▸ 𝟙 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A)
    → (∀ (eqM : n = 0) (a_7 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A.indUnit b a = a_7
        → eqM ▸ A⌈b⌉₀ = A_1
        → ε ⊢ a_7 ≡ a_7 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_7 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A.indUnit b a = a_7
        → eqM ▸ A⌈b⌉₀ = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_7 ≡ a_7 ∶ A_1 :=
  by
    intro n Γ A a b hA haA hb1 ihA ihaA ihb1
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.unit_elim_eq
      · rw [←empty_expand_context (Γ := ε ⬝ 𝟙)]
        apply And.right (And.right ihA)
        repeat' rfl
      · apply And.left ihaA
        repeat' rfl
      · apply And.left ihb1
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihaA)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.unit_elim_eq
      · rw [extend_expand_context]
        apply And.right (And.right ihA)
        repeat' rfl
      · apply And.right (And.right ihaA)
        repeat' rfl
      · apply And.right (And.right ihb1)
        repeat' rfl

theorem defeq_refl_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
    Γ ⬝ 𝟘 ⊢ A type
    → (Γ ⊢ b ∶ 𝟘)
    → ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0),
        eqM ▸ Γ ⬝ 𝟘 = ε
        → eqM ▸ A = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → ((∀ (eqM : n = 0) (a A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ b = a
        → eqM ▸ 𝟘 = A
        → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ b = a
        → eqM ▸ 𝟘 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A)
    → (∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A.indEmpty b = a
        → eqM ▸ A⌈b⌉₀ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A.indEmpty b = a
        → eqM ▸ A⌈b⌉₀ = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n Γ A b hA hb0 ihA ihb0
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.empty_elim_eq
      · rw [←empty_expand_context (Γ := ε ⬝ 𝟘)]
        apply And.right (And.right ihA)
        repeat' rfl
      · apply And.left ihb0
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihb0)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.empty_elim_eq
      · rw [extend_expand_context]
        apply And.right (And.right ihA)
        repeat' rfl
      · apply And.right (And.right ihb0)
        repeat' rfl

theorem defeq_refl_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
    (Γ ⊢ f ∶ ΠA;B)
    → (Γ ⊢ a ∶ A)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ f = a
        → (eqM ▸ ΠA;B) = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type) ∧
      ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ f = a
        → (eqM ▸ ΠA;B) = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n = 0) (a_4 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a = a_4
        → eqM ▸ A = A_1
        → ε ⊢ a_4 ≡ a_4 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_4 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a = a_4
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_4 ≡ a_4 ∶ A_1)
    → (∀ (eqM : n = 0) (a_5 A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ f◃a = a_5
        → eqM ▸ B⌈a⌉₀ = A
        → ε ⊢ a_5 ≡ a_5 ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ f◃a = a_5
        → eqM ▸ B⌈a⌉₀ = A
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A :=
  by
    intro n Γ f A B a hfPi haA ihfPi ihaA
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.pi_elim_eq
      · apply And.left ihfPi
        repeat' rfl
      · apply And.left ihaA
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihaA)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.pi_elim_eq
      · apply And.right (And.right ihfPi)
        repeat' rfl
      · apply And.right (And.right ihaA)
        repeat' rfl

theorem defeq_refl_sigma_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
    (Γ ⬝ ΣA;B) ⊢ C type
    → (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
    → (Γ ⊢ p ∶ ΣA;B)
    → ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0),
        (eqM ▸ Γ ⬝ ΣA;B) = ε
        → eqM ▸ C = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B_1 : Tm m),
        (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ B_1 ⊗ Δ
        → Γ_1 ⊢ B_1 ≡ B_1 type) ∧
      ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
        (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ C = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → ((∀ (eqM : n + 1 + 1 = 0) (a A_1 : Tm 0),
        eqM ▸ Γ ⬝ A ⬝ B = ε
        → eqM ▸ c = a
        → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 = z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ
        → Γ_1 ⊢ B_1 ≡ B_1 type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ c = a
        → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ p = a
        → (eqM ▸ ΣA;B) = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ p = a
        → (eqM ▸ ΣA;B) = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → (∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A.indSigma B C c p = a
        → eqM ▸ C⌈p⌉₀ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ A.indSigma B C c p = a
        → eqM ▸ C⌈p⌉₀ = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n Γ' A B p C c hC hcC hpSi ihC ihcC ihpSi
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.sigma_elim_eq
      · rw [←empty_expand_context (Γ := ε ⬝ (ΣA;B))]
        apply And.right (And.right ihC)
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε ⬝ A ⬝ B)]
        apply And.right (And.right ihcC)
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε)]
        apply And.left (And.right ihcC)
        rotate_left
        · apply 2
        · apply CtxGen.start ⊙ B
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply And.left (And.right ihcC)
        rotate_left
        · apply 2
        · apply CtxGen.start
        repeat' rfl
      · apply And.left ihpSi
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihpSi)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.sigma_elim_eq
      · rw [extend_expand_context]
        apply And.right (And.right ihC)
        repeat' rfl
      · simp [extend_expand_context]
        apply And.right (And.right ihcC)
        repeat' rfl
      · apply And.left (And.right ihcC)
        rotate_left
        · apply n + 2
        · apply CtxGen.start ⊙ B
        repeat' rfl
      · apply And.left (And.right ihcC)
        rotate_left
        · apply n + 2
        · apply CtxGen.start
        repeat' rfl
      · apply And.right (And.right ihpSi)
        repeat' rfl

theorem defeq_refl_nat_elim :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ∶ 𝒩)
    → ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0),
        eqM ▸ Γ ⬝ 𝒩 = ε
        → eqM ▸ A = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ z = a
        → eqM ▸ A⌈𝓏⌉₀ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z_1 : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z_1) (eqM : n = z_1) (a A_1 : Tm z_1) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ z = a
        → eqM ▸ A⌈𝓏⌉₀ = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n + 1 + 1 = 0) (a A_1 : Tm 0),
        eqM ▸ Γ ⬝ 𝒩 ⬝ A = ε
        → eqM ▸ s = a
        → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ s = a
        → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n = 0) (a A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ x = a
        → eqM ▸ 𝒩 = A
        → ε ⊢ a ≡ a ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ x = a
        → eqM ▸ 𝒩 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A)
    → (∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A.indNat z s x = a
        → eqM ▸ A⌈x⌉₀ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z_1 : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z_1) (eqM : n = z_1) (a A_1 : Tm z_1) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A.indNat z s x = a
        → eqM ▸ A⌈x⌉₀ = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1 :=
  by
    intro n Γ z x A s hA hzA hsA hxNat ihA ihzA ihsA ihxNat
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.nat_elim_eq
      · rw [←empty_expand_context (Γ := ε ⬝ 𝒩 )]
        apply And.right (And.right ihA)
        repeat' rfl
      · apply And.left ihzA
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε ⬝ 𝒩  ⬝ A)]
        apply And.right (And.right ihsA)
        repeat' rfl
      · apply And.left ihxNat
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihxNat)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.nat_elim_eq
      · rw [extend_expand_context]
        apply And.right (And.right ihA)
        repeat' rfl
      · apply And.right (And.right ihzA)
        repeat' rfl
      · rw [extend_expand_context]
        rw [extend_expand_context]
        apply And.right (And.right ihsA)
        repeat' rfl
      · apply And.right (And.right ihxNat)
        repeat' rfl

theorem defeq_refl_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a a' p : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
    → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → (Γ ⊢ p ∶ a ≃[A] a')
    → ((∀ (eqM : n + 1 + 1 + 1 = 0) (A_1 : Tm 0),
        (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = ε
        → eqM ▸ B = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 + 1 = z) (B : Tm m),
        (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 + 1 + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
        (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ B = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → ((∀ (eqM : n + 1 = 0) (a A_1 : Tm 0),
        eqM ▸ Γ ⬝ A = ε
        → eqM ▸ b = a
        → eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (a A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ b = a
        → eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n = 0) (a_6 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a = a_6
        → eqM ▸ A = A_1
        → ε ⊢ a_6 ≡ a_6 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_6 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a = a_6
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_6 ≡ a_6 ∶ A_1)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a' = a
        → eqM ▸ A = A_1
        → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a' = a
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → ((∀ (eqM : n = 0) (a_8 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ p = a_8
        → (eqM ▸ a ≃[A] a') = A_1
        → ε ⊢ a_8 ≡ a_8 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_8 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ p = a_8
        → (eqM ▸ a ≃[A] a') = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_8 ≡ a_8 ∶ A_1)
    → (∀ (eqM : n = 0) (a_9 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A.j B b a a' p = a_9
        → eqM ▸ B⌈(ₛidₚ)⋄ a⋄ a'⋄ p⌉ = A_1
        → ε ⊢ a_9 ≡ a_9 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_9 A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ A.j B b a a' p = a_9
        → eqM ▸ B⌈(ₛidₚ)⋄ a⋄ a'⋄ p⌉ = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_9 ≡ a_9 ∶ A_1 :=
  by
    intro n Γ A B b a a' p hB hbB haA haA' hpId ihB ihbB ihaA ihaA' ihpId
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.iden_elim_eq
      · rw [←empty_expand_context (Γ := (ε ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)))]
        apply And.right (And.right ihB)
        repeat' rfl
      · rw [←empty_expand_context (Γ := (ε ⬝ A))]
        apply And.right (And.right ihbB)
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε)]
        apply And.left (And.right ihB)
        rotate_left
        · apply 3
        · apply CtxGen.start ⊙ A⌊↑ₚidₚ⌋ ⊙ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)
        repeat' rfl
      · apply And.left (ihaA)
        repeat' rfl
      · apply And.left (ihaA')
        repeat' rfl
      · apply And.left (ihpId)
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihaA)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.iden_elim_eq
      · simp [extend_expand_context]
        apply And.right (And.right ihB)
        repeat' rfl
      · simp [extend_expand_context]
        apply And.right (And.right ihbB)
        repeat' rfl
      · apply And.left (And.right ihB)
        rotate_left
        · apply n + 3
        · apply CtxGen.start ⊙ A⌊↑ₚidₚ⌋ ⊙ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)
        repeat' rfl
      · apply And.right (And.right ihaA)
        repeat' rfl
      · apply And.right (And.right ihaA')
        repeat' rfl
      · apply And.right (And.right ihpId)
        repeat' rfl

theorem defeq_refl_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
    (Γ ⊢ a ∶ A)
    → Γ ⊢ A ≡ B type
    → ((∀ (eqM : n = 0) (a_3 A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a = a_3
        → eqM ▸ A = A_1 → ε ⊢ a_3 ≡ a_3 ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_3 A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ a = a_3
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a_3 ≡ a_3 ∶ A_1)
    → Γ ⊢ A ≡ B type
    → (∀ (eqM : n = 0) (a_5 A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ a = a_5
        → eqM ▸ B = A
        → ε ⊢ a_5 ≡ a_5 ∶ A)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_5 A : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ a = a_5
        → eqM ▸ B = A
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ a_5 ≡ a_5 ∶ A :=
  by
    intro n Γ a A B haA hAB ihaA ihAB
    repeat' apply And.intro
    · intro heqM t T heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.ty_conv_eq
      · apply And.left ihaA
        repeat' rfl
      · apply hAB
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihaA)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM t T S heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.ty_conv_eq
      · apply And.right (And.right ihaA)
        repeat' rfl
      · apply hAB
