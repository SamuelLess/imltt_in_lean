import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.admissable.Weakening

theorem context_conversion_var_eq :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) {S S' : Tm l} (A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ v(0) = a
    → eqM ▸ v(0) = a'
    → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' A hA ihA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases Δ with
    | start =>
      cases heqΓ
      apply IsEqualTerm.ty_conv_eq
      · apply IsEqualTerm.var_eq hS'
      · apply weakening_type_eq
        · apply IsEqualType.type_symm hSS
        · apply hS'
    | expand Δ' R =>
      cases heqΓ
      apply IsEqualTerm.var_eq
      apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_weak_eq :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ≡ v(i) ∶ A)
    → Γ ⊢ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ v(i) = a
      → eqM ▸ v(i) = a'
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) {S S' : Tm l} (A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a
    → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a'
    → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n x Γ' A B hvvA hB ihvvA ihB m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases Δ with
    | start =>
      cases heqΓ
      apply IsEqualTerm.weak_eq
      · apply hvvA
      · apply hS'
    | expand Δ' R =>
      cases heqΓ
      apply IsEqualTerm.weak_eq
      · apply ihvvA
        · apply hSS
        · apply hS
        · apply hS'
        repeat' rfl
      · apply ihB
        · apply hSS
        · apply hS
        · apply hS'
        repeat' rfl

theorem context_conversion_unit_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
    Γ ⬝ 𝟙 ⊢ A type
    → (Γ ⊢ a ∶ A⌈⋆⌉₀)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_4 A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ A⌈⋆⌉₀ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_4 ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.indUnit ⋆ a = a_5
    → eqM ▸ a = a'
    → eqM ▸ A⌈⋆⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ≡ a' ∶ A_1 :=
  by
    intro n Γ' A a hA haA ihA ihaA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.unit_comp
    · rw [extend_expand_context]
      apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_pi_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
    (Γ ⬝ A ⊢ b ∶ B)
    → (Γ ⊢ a ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ B = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_4 A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_4 ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ (λA; b)◃a = a_5
    → eqM ▸ b⌈a⌉₀ = a'
    → eqM ▸ B⌈a⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ≡ a' ∶ A_1 :=
  by
    intro n Γ' A b B a hbB haA ihbB ihaA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.pi_comp
    · rw [extend_expand_context]
      apply ihbB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_sigma_comp :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
    (Γ ⬝ ΣA;B) ⊢ C type
    → (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ b ∶ B⌈a⌉₀)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ C = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ c = a
      → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_7 A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_7
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_7 ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_8 A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a_8
      → eqM ▸ B⌈a⌉₀ = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_8 ∶ A)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_9 a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.indSigma B C c (a&b) = a_9
    → eqM ▸ c⌈(ₛidₚ)⋄ a⋄ b⌉ = a'
    → eqM ▸ C⌈a&b⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_9 ≡ a' ∶ A_1 :=
  by
    intro n Γ' a A b B C c hC hcC haA hbB ihC ihcC ihaA ihbB m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.sigma_comp
    · rw [extend_expand_context]
      apply ihC
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · simp [extend_expand_context]
      apply ihcC
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihbB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_nat_zero_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ 𝓏 ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ z = a
      → eqM ▸ A⌈𝓏⌉₀ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ s = a
      → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ 𝓏 = a
      → eqM ▸ 𝒩 = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.indNat z s 𝓏 = a
    → eqM ▸ z = a'
    → eqM ▸ A⌈𝓏⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' z A s hA hzA hsA hzNat ihA ihzA ihsA ihzNat m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_zero_comp
    · rw [extend_expand_context]
      apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihzA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      rw [extend_expand_context]
      apply ihsA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihzNat
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_nat_succ_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ z = a
      → eqM ▸ A⌈𝓏⌉₀ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ s = a
      → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ x = a
      → eqM ▸ 𝒩 = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.indNat z s 𝓈(x) = a
    → eqM ▸ s⌈(ₛidₚ)⋄ x⋄ A.indNat z s x⌉ = a'
    → eqM ▸ A⌈𝓈(x)⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' z x A s hA hzA hsA hsNat ihA ihzA ihsA ihsNat m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_succ_comp
    · rw [extend_expand_context]
      apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihzA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      rw [extend_expand_context]
      apply ihsA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihsNat
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_iden_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
    → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → (Γ ⊢ a ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 + 1 = m) {S S' : Tm l} (A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_7 A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_7
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_7 ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_9 a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.j B b a a (A.refl a) = a_9
    → eqM ▸ b⌈a⌉₀ = a'
    → eqM ▸ B⌈(ₛidₚ)⋄ a⋄ a⋄ A.refl a⌉ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_9 ≡ a' ∶ A_1 :=
  by
    intro n Γ' A B b a hB hbB haA ihB ihbB ihaA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.iden_comp
    · simp [extend_expand_context]
      apply ihB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · simp [extend_expand_context]
      apply ihbB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_unit_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → Γ_1 ⬝ S' ⊗ Δ ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ ⋆ = a
    → eqM ▸ ⋆ = a'
    → eqM ▸ 𝟙 = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.unit_intro_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_unit_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
    Γ ⬝ 𝟙 ⊢ A ≡ A' type
    → (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀)
    → (Γ ⊢ b ≡ b' ∶ 𝟙)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_5
      → eqM ▸ a' = a'_1
      → eqM ▸ A⌈⋆⌉₀ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ≡ a'_1 ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ b' = a'
      → eqM ▸ 𝟙 = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_7 a'_1 A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.indUnit b a = a_7
    → eqM ▸ A'.indUnit b' a' = a'_1
    → eqM ▸ A⌈b⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_7 ≡ a'_1 ∶ A_1 :=
  by
    intro n Γ' A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihbb1 m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.unit_elim_eq
    · rw [extend_expand_context]
      apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihbb1
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_empty_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
    Γ ⬝ 𝟘 ⊢ A ≡ A' type
    → (Γ ⊢ b ≡ b' ∶ 𝟘)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ b' = a'
      → eqM ▸ 𝟘 = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.indEmpty b = a
    → eqM ▸ A'.indEmpty b' = a'
    → eqM ▸ A⌈b⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' A A' b b' hAA hbb0 ihAA ihbb0 m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.empty_elim_eq
    · rw [extend_expand_context]
      apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihbb0
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_pi_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B)
    → Γ ⊢ A ≡ A' type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ b' = a'
      → eqM ▸ B = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → (eqM ▸ λA; b) = a
    → (eqM ▸ λA'; b') = a'
    → (eqM ▸ ΠA;B) = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' A A' b b' B hbbB hAA ihbbB ihAA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.pi_intro_eq
    · rw [extend_expand_context]
      apply ihbbB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_pi_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
    (Γ ⊢ f ≡ f' ∶ ΠA;B)
    → (Γ ⊢ a ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ f = a
      → eqM ▸ f' = a'
      → (eqM ▸ ΠA;B) = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_4 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ a' = a'_1
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_4 ≡ a'_1 ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 a'_1 A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ f◃a = a_5
    → eqM ▸ f'◃a' = a'_1
    → eqM ▸ B⌈a⌉₀ = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ≡ a'_1 ∶ A :=
  by
    intro n Γ' f f' A B a a' hffPi haaA ihffPi ihaaA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.pi_elim_eq
    · apply ihffPi
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_sigma_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ≡ a' ∶ A)
    → (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀)
    → Γ ⬝ A ⊢ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_4 a'_1 A_1 : Tm m), Γ_1 ⊢ S ≡ S' type →
      Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ a' = a'_1
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_4 ≡ a'_1 ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 a' A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a_5
      → eqM ▸ b' = a'
      → eqM ▸ B⌈a⌉₀ = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_7 a'_1 A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ a&b = a_7
    → eqM ▸ a'&b' = a'_1
    → (eqM ▸ ΣA;B) = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_7 ≡ a'_1 ∶ A_1 :=
  by
    intro n Γ' a a' A b b' B haaA hbbB hB ihaaA ihbbB ihB m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.sigma_intro_eq
    · apply ihaaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihbbB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_sigma_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)}
      {c c' : Tm (n + 1 + 1)},
    (Γ ⬝ ΣA;B) ⊢ C ≡ C' type
    → (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
    → Γ ⊢ A ≡ A' type
    → Γ ⬝ A ⊢ B ≡ B' type
    → (Γ ⊢ p ≡ p' ∶ ΣA;B)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ C = A_1
      → eqM ▸ C' = A'
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ c = a
      → eqM ▸ c' = a'
      → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = A_1
      → eqM ▸ B' = A'
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ p = a
      → eqM ▸ p' = a'
      → (eqM ▸ ΣA;B) = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.indSigma B C c p = a
    → eqM ▸ A'.indSigma B' C' c' p' = a'
    → eqM ▸ C⌈p⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' A B A' B' p p' C C' c c' hCC hccC hAA hBB hppSi ihCC ihccC ihAA ihBB ihppSi
    intro m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.sigma_elim_eq
    · simp [extend_expand_context]
      apply ihCC
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · simp [extend_expand_context]
      apply ihccC
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihBB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihppSi
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_nat_zero_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → Γ_1 ⬝ S' ⊗ Δ ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝓏 = a
    → eqM ▸ 𝓏 = a'
    → eqM ▸ 𝒩 = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_zero_intro_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_nat_succ_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n}{x x' : Tm n},
    (Γ ⊢ x ≡ x' ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ x = a
      → eqM ▸ x' = a'
      → eqM ▸ 𝒩 = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝓈(x) = a
    → eqM ▸ 𝓈(x') = a'
    → eqM ▸ 𝒩 = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A :=
  by
    intro n Γ' x x' hxxNat ihxxNat m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_succ_intro_eq
    apply ihxxNat
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_nat_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {z z' x x' : Tm n} {A A' : Tm (n + 1)} {s s' : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A ≡ A' type
    → (Γ ⊢ z ≡ z' ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ≡ s' ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ≡ x' ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ z = a
      → eqM ▸ z' = a'
      → eqM ▸ A⌈𝓏⌉₀ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ s = a
      → eqM ▸ s' = a'
      → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ x = a
      → eqM ▸ x' = a'
      → eqM ▸ 𝒩 = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.indNat z s x = a
    → eqM ▸ A'.indNat z' s' x' = a'
    → eqM ▸ A⌈x⌉₀ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' z z' x x' A A' s s' hAA hzzA hssA hxxNat ihAA ihzzA ihssA ihxxNat m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_elim_eq
    · rw [extend_expand_context]
      apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihzzA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      rw [extend_expand_context]
      apply ihssA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihxxNat
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_iden_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
    Γ ⊢ A ≡ A' type
    → (Γ ⊢ a ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_4 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ a' = a'_1
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_4 ≡ a'_1 ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 a'_1 A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.refl a = a_5
    → eqM ▸ A'.refl a' = a'_1
    → (eqM ▸ a ≃[A] a) = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ≡ a'_1 ∶ A_1 :=
  by
    intro n Γ' A A' a a' hAA haaA ihAA ihaaA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.iden_intro_eq
    · apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_iden_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' : Tm (n + 1)} {a₁ a₃ A' a₂ a₄ p p' : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type
    → (Γ ⬝ A ⊢ b ≡ b' ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → Γ ⊢ A ≡ A' type
    → (Γ ⊢ a₁ ≡ a₂ ∶ A)
    → (Γ ⊢ a₃ ≡ a₄ ∶ A')
    → (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 + 1 = m) (S S' : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = A_1
      → eqM ▸ B' = A'
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ b' = a'
      → eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a₁ = a
      → eqM ▸ a₂ = a'
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a₃ = a
      → eqM ▸ a₄ = a'
      → eqM ▸ A' = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ p = a
      → eqM ▸ p' = a'
      → (eqM ▸ a₁ ≃[A] a₃) = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A.j B b a₁ a₃ p = a
    → eqM ▸ A'.j B' b' a₂ a₄ p' = a'
    → eqM ▸ B⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉ = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1:=
  by
    intro n Γ' A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hAA haaA haaA' hppId ihBB ihbbB ihAA ihaaA ihaaA' ihppId
    intro m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.iden_elim_eq
    · simp [extend_expand_context]
      apply ihBB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · simp [extend_expand_context]
      apply ihbbB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihAA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA'
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihppId
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_univ_unit_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → Γ_1 ⬝ S' ⊗ Δ ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝟙 = a
    → eqM ▸ 𝟙 = a'
    → eqM ▸ 𝒰 = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_unit_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_univ_empty_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → Γ_1 ⬝ S' ⊗ Δ ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝟘 = a
    → eqM ▸ 𝟘 = a'
    → eqM ▸ 𝒰 = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_empty_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_univ_pi_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ A' = a'
      → eqM ▸ 𝒰 = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = a
      → eqM ▸ B' = a'
      → eqM ▸ 𝒰 = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → (eqM ▸ ΠA;B) = a
    → (eqM ▸ ΠA';B') = a'
    → eqM ▸ 𝒰 = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_pi_eq
    · apply ihAAU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihBBU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_univ_sigma_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ A' = a'
      → eqM ▸ 𝒰 = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = a
      → eqM ▸ B' = a'
      → eqM ▸ 𝒰 = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → (eqM ▸ ΣA;B) = a
    → (eqM ▸ ΣA';B') = a'
    → eqM ▸ 𝒰 = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_sigma_eq
    · apply ihAAU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihBBU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_univ_nat_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → Γ_1 ⬝ S' ⊗ Δ ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝒩 = a
    → eqM ▸ 𝒩 = a'
    → eqM ▸ 𝒰 = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_nat_eq
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_univ_iden_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⊢ a₁ ≡ a₂ ∶ A)
    → (Γ ⊢ a₃ ≡ a₄ ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ A' = a'
      → eqM ▸ 𝒰 = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a₁ = a
      → eqM ▸ a₂ = a'
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a₃ = a
      → eqM ▸ a₄ = a'
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → (eqM ▸ a₁ ≃[A] a₃) = a
    → (eqM ▸ a₂ ≃[A'] a₄) = a'
    → eqM ▸ 𝒰 = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A_1 :=
  by
    intro n Γ' A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' ihAAU ihaaA ihaaA' m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_iden_eq
    · apply ihAAU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaaA'
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_ty_conv_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
    (Γ ⊢ a ≡ b ∶ A)
    → Γ ⊢ A ≡ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_3 a' A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_3
      → eqM ▸ b = a'
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_3 ≡ a' ∶ A_1)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ B = A'
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 a' A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ a = a_5
    → eqM ▸ b = a'
    → eqM ▸ B = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ≡ a' ∶ A :=
  by
    intro n Γ' a b A B habA hAB ihabA ihAB m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.ty_conv_eq
    · apply ihabA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihAB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_term_symm :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A : Tm n},
    (Γ ⊢ a ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_1 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_1
      → eqM ▸ a' = a'_1
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_1 ≡ a'_1 ∶ A_1)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_2 a'_1 A_1 : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ a' = a_2
    → eqM ▸ a = a'_1
    → eqM ▸ A = A_1
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_2 ≡ a'_1 ∶ A_1 :=
  by
    intro n Γ' a a' A haaA ihaaA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.term_symm
    apply ihaaA
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_term_trans :
    ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
    (Γ ⊢ a ≡ b ∶ T)
    → (Γ ⊢ b ≡ c ∶ T)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_1 a' A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_1
      → eqM ▸ b = a'
      → eqM ▸ T = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a_1 ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ c = a'
      → eqM ▸ T = A
      → Γ_1 ⬝ S' ⊗ Δ ⊢ a ≡ a' ∶ A)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_3 a' A : Tm m),
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ a = a_3
    → eqM ▸ c = a'
    → eqM ▸ T = A
    → Γ_1 ⬝ S' ⊗ Δ ⊢ a_3 ≡ a' ∶ A :=
  by
    intro n Γ' A a b c habA hbcA ihabA ihbcA m l Γ Δ heqM S S' t t' T hSS hS hS' heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.term_trans
    · apply ihabA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihbcA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
