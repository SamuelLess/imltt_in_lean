import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Contexts
import IMLTT.untyped.proofs.Contexts

import IMLTT.typed.JudgmentsAndRules

theorem defeq_refl_unit_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ 𝟙 = A → ε ⊢ A ≡ A type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝟙 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.unit_form_eq hiC
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
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.unit_form_eq hiC

theorem defeq_refl_empty_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ 𝟘 = A
        → ε ⊢ A ≡ A type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝟘 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.empty_form_eq hiC
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
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.empty_form_eq hiC

theorem defeq_refl_pi_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type
    → Γ ⬝ A ⊢ B type
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
    → (∀ (eqM : n = 0) (A_1 : Tm 0),
        eqM ▸ Γ = ε
        → (eqM ▸ ΠA;B) = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → (eqM ▸ ΠA;B) = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type :=
  by
    intro n Γ A B hA hB ihA ihB
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.pi_form_eq
      · apply And.left ihA
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply And.right (And.right ihB)
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihA)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.pi_form_eq
      · apply And.right (And.right ihA)
        repeat' rfl
      · rw [extend_expand_context]
        apply And.right (And.right ihB)
        repeat' rfl


theorem defeq_refl_sigma_form :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    Γ ⊢ A type
    → Γ ⬝ A ⊢ B type
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
    → ((∀ (eqM : n + 1 = 0) (A_1 : Tm 0), eqM ▸ Γ ⬝ A = ε → eqM ▸ B = A_1 → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (B : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n + 1 = z) (A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ B_1 ⊗ Δ
        → eqM ▸ B = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → (∀ (eqM : n = 0) (A_1 : Tm 0),
        eqM ▸ Γ = ε
        → (eqM ▸ ΣA;B) = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B_1 : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B_1 ⊗ Δ
        → (eqM ▸ ΣA;B) = A_1
        → Γ_1 ⬝ B_1 ⊗ Δ ⊢ A_1 ≡ A_1 type :=
  by
    intro n Γ A B hA hB ihA ihB
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.sigma_form_eq
      · apply And.left ihA
        repeat' rfl
      · rw [←empty_expand_context (Γ := ε ⬝ A)]
        apply And.right (And.right ihB)
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihA)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.sigma_form_eq
      · apply And.right (And.right ihA)
        repeat' rfl
      · rw [extend_expand_context]
        apply And.right (And.right ihB)
        repeat' rfl

theorem defeq_refl_nat_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (A : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ 𝒩 = A
        → ε ⊢ A ≡ A type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝒩 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.nat_form_eq hiC
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
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.nat_form_eq hiC


theorem defeq_refl_iden_form :
    ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
    Γ ⊢ A type
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
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
    → (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → (eqM ▸ a ≃[A] a') = A_1 → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → (eqM ▸ a ≃[A] a') = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type :=
  by
    intro n Γ' a A a' hA haA haA' ihA ihaA ihaA'
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.iden_form_eq
      · apply And.left ihA
        repeat' rfl
      · apply And.left ihaA
        repeat' rfl
      · apply And.left ihaA'
        repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihA)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.iden_form_eq
      · apply And.right (And.right ihA)
        repeat' rfl
      · apply And.right (And.right ihaA)
        repeat' rfl
      · apply And.right (And.right ihaA')
        repeat' rfl

theorem defeq_refl_univ_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → (∀ (eqM : n = 0) (A : Tm 0), eqM ▸ Γ = ε → eqM ▸ 𝒰 = A → ε ⊢ A ≡ A type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ 𝒰 = A
        → Γ_1 ⬝ B ⊗ Δ ⊢ A ≡ A type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.univ_form_eq hiC
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
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.univ_form_eq hiC

theorem defeq_refl_univ_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
    (Γ ⊢ A ∶ 𝒰)
    → ((∀ (eqM : n = 0) (a A_1 : Tm 0),
        eqM ▸ Γ = ε → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → ε ⊢ a ≡ a ∶ A_1)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = a
        → eqM ▸ 𝒰 = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ a ≡ a ∶ A_1)
    → (∀ (eqM : n = 0) (A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type :=
  by
    intro n Γ' A hAU ihAU
    repeat' apply And.intro
    · intro heqM T heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.univ_elim_eq
      apply And.left ihAU
      repeat' rfl
    · intro m z Γ Δ heqM S heqΓ
      cases heqM
      cases heqΓ
      apply And.left (And.right ihAU)
      rotate_left
      · apply n
      · apply Δ
      repeat' rfl
    · intro m z Γ Δ heqM T S heqΓ heqT
      cases heqM
      cases heqΓ
      cases heqT
      apply IsEqualType.univ_elim_eq
      apply And.right (And.right ihAU)
      repeat' rfl
