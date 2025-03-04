import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

theorem context_conversion_var :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
      Γ ⊢ A type →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) {S S' : Tm l} (A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ v(0) = a → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1 :=
  by
    intro n Γ' A hA ihA m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqt
    cases heqT
    cases Δ with
    | start =>
      cases heqΓ
      apply HasType.ty_conv
      · apply HasType.var hS'
      · apply weakening_type_eq
        · apply IsEqualType.type_symm hSS
        · apply hS'
    | expand Δ' R =>
      cases heqΓ
      apply HasType.var
      apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_weak :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ∶ A) →
    Γ ⊢ B type →
      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (S S' : Tm l) (a A_1 : Tm m),
          Γ_1 ⊢ S ≡ S' type →
            Γ_1 ⊢ S type →
              Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ v(i) = a → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) {S S' : Tm l} (A : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A → Γ_1 ⬝ S' ⊗ Δ ⊢ A type) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type →
                  eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1 :=
  by
    intro n x Γ A B hvA hB ihvA ihB m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqt
    cases heqT
    cases Δ with
    | start =>
      cases heqΓ
      apply HasType.weak
      · apply hvA
      · apply hS'
    | expand Δ' R =>
      cases heqΓ
      apply HasType.weak
      · apply ihvA
        · apply hSS
        · apply hS
        · apply hS'
        repeat' rfl
      · apply ihB
        · apply hSS
        · apply hS
        · apply hS'
        repeat' rfl

theorem context_conversion_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ ⋆ = a → eqM ▸ 𝟙 = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.unit_intro
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
      (Γ ⬝ A ⊢ b ∶ B) →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ b = a → eqM ▸ B = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ λA; b) = a → (eqM ▸ ΠA;B) = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1 :=
  by
    intro n Γ' A b B hbB ihbB m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.pi_intro
    rw [extend_expand_context]
    apply ihbB
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
  (Γ ⊢ a ∶ A) →
    (Γ ⊢ b ∶ B⌈a⌉₀) →
      Γ ⬝ A ⊢ B type →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_4 A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_4 → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_4 ∶ A_1) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 A : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type →
                  Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ b = a_5 → eqM ▸ B⌈a⌉₀ = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ∶ A) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_7 A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a&b = a_7 → (eqM ▸ ΣA;B) = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_7 ∶ A_1 :=
  by
    intro n Γ' a A b B haA hbB hB ihaA ihbB ihB m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.sigma_intro
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
    · rw [extend_expand_context]
      apply ihB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
      Γ ⊢ A type →
    (Γ ⊢ a ∶ A) →
      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
          Γ_1 ⊢ S ≡ S' type →
            Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_4 A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_4 → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_4 ∶ A_1) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type →
                Γ_1 ⊢ S' type →
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A.refl a = a_5 → (eqM ▸ a ≃[A] a) = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ∶ A_1 :=
  by
    intro n Γ' A a hA haA ihA ihaA m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.iden_intro
    · apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝟙 = a → eqM ▸ 𝒰 = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_unit
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n},
      Γ ctx →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
            Γ_1 ⊢ S ≡ S' type → Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → Γ_1 ⬝ S' ⊗ Δ ctx) →
          ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ 𝟘 = a → eqM ▸ 𝒰 = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_empty
    apply ihiC
    · apply hSS
    · apply hS
    · apply hS'
    repeat' rfl

theorem context_conversion_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
      (Γ ⊢ A ∶ 𝒰) →
        (Γ ⬝ A ⊢ B ∶ 𝒰) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type →
                  Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ ΠA;B) = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1 :=
  by
    intro n Γ' A B hAU hBU ihAU ihBU m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_pi
    · apply ihAU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihBU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
      (Γ ⊢ A ∶ 𝒰) →
        (Γ ⬝ A ⊢ B ∶ 𝒰) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type →
                  Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ ΣA;B) = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1 :=
  by
    intro n Γ' A B hAU hBU ihAU ihBU m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_sigma
    · apply ihAU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihBU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
      (Γ ⊢ A ∶ 𝒰) →
        (Γ ⊢ a ∶ A) →
          (Γ ⊢ a' ∶ A) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
              (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 A_1 : Tm m),
                  Γ_1 ⊢ S ≡ S' type →
                    Γ_1 ⊢ S type →
                      Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ∶ A_1) →
                (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a' = a → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
                  ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_7 A_1 : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type →
                          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (eqM ▸ a ≃[A] a') = a_7 → eqM ▸ 𝒰 = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_7 ∶ A_1 :=
  by
    intro n Γ' A a a' hAU haA haA' ihAU ihaA ihaA' m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_iden
    · apply ihAU
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA'
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_unit_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type →
    (Γ ⊢ a ∶ A⌈⋆⌉₀) →
      (Γ ⊢ b ∶ 𝟙) →
        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
            Γ_1 ⊢ S ≡ S' type →
              Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 A_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type →
                  Γ_1 ⊢ S' type →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ A⌈⋆⌉₀ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ∶ A_1) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ b = a → eqM ▸ 𝟙 = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_7 A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A.indUnit b a = a_7 → eqM ▸ A⌈b⌉₀ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_7 ∶ A_1 :=
  by
    intro n Γ' A a b hA haA hb1 ihA ihaA ihb1 m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.unit_elim
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
    · apply ihb1
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
      Γ ⬝ 𝟘 ⊢ A type →
        (Γ ⊢ b ∶ 𝟘) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type → Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ b = a → eqM ▸ 𝟘 = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A.indEmpty b = a → eqM ▸ A⌈b⌉₀ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1 :=
  by
    intro n Γ' A b hA hb0 ihA ihb0 m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.empty_elim
    · rw [extend_expand_context]
      apply ihA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihb0
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
      (Γ ⊢ f ∶ ΠA;B) →
        (Γ ⊢ a ∶ A) →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type →
                  Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ f = a → (eqM ▸ ΠA;B) = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_4 A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_4 → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_4 ∶ A_1) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 A : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ f◃a = a_5 → eqM ▸ B⌈a⌉₀ = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ∶ A :=
  by
    intro n Γ' f A B a hfPi haA ihfPi ihaA m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.pi_elim
    · apply ihfPi
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_sigma_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
      (Γ ⊢ p ∶ ΣA;B) →
        (Γ ⬝ ΣA;B) ⊢ C type →
          (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ p = a → (eqM ▸ ΣA;B) = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
              (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) {S S' : Tm l} (A_1 : Tm m),
                  Γ_1 ⊢ S ≡ S' type →
                    Γ_1 ⊢ S type →
                      Γ_1 ⊢ S' type → (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ → eqM ▸ C = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
                (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m) (S S' : Tm l) (a A_1 : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type →
                          eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                            eqM ▸ c = a → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
                  ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type →
                          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A.indSigma B C c p = a → eqM ▸ C⌈p⌉₀ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1 :=
  by
    intro n Γ' A B p C c hpSi hC hcC ihpSi ihC ihcC m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.sigma_elim
    · apply ihpSi
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      apply ihC
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · rw [extend_expand_context]
      rw [extend_expand_context]
      apply ihcC
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a a' p : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
    (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (Γ ⊢ p ∶ a ≃[A] a') →
            Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
              Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type →
                (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 + 1 = m) {S S' : Tm l}
                    (A_1 : Tm m),
                    Γ_1 ⊢ S ≡ S' type →
                      Γ_1 ⊢ S type →
                        Γ_1 ⊢ S' type →
                          (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                            eqM ▸ B = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
                  (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_7 A_1 : Tm m),
                      Γ_1 ⊢ S ≡ S' type →
                        Γ_1 ⊢ S type →
                          Γ_1 ⊢ S' type →
                            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                              eqM ▸ b = a_7 → eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_7 ∶ A_1) →
                    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_8 A_1 : Tm m),
                        Γ_1 ⊢ S ≡ S' type →
                          Γ_1 ⊢ S type →
                            Γ_1 ⊢ S' type →
                              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_8 → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_8 ∶ A_1) →
                      (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a A_1 : Tm m),
                          Γ_1 ⊢ S ≡ S' type →
                            Γ_1 ⊢ S type →
                              Γ_1 ⊢ S' type →
                                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a' = a → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a ∶ A_1) →
                        (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l)
                            (a_10 A_1 : Tm m),
                            Γ_1 ⊢ S ≡ S' type →
                              Γ_1 ⊢ S type →
                                Γ_1 ⊢ S' type →
                                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                    eqM ▸ p = a_10 → (eqM ▸ a ≃[A] a') = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_10 ∶ A_1) →
                          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
                              Γ_1 ⊢ S ≡ S' type →
                                Γ_1 ⊢ S type →
                                  Γ_1 ⊢ S' type →
                                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                      eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type) →
                            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A : Tm m),
                                Γ_1 ⊢ S ≡ S' type →
                                  Γ_1 ⊢ S type →
                                    Γ_1 ⊢ S' type →
                                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A → Γ_1 ⬝ S' ⊗ Δ ⊢ A type) →
                              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l)
                                (a_13 A_1 : Tm m),
                                Γ_1 ⊢ S ≡ S' type →
                                  Γ_1 ⊢ S type →
                                    Γ_1 ⊢ S' type →
                                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                        eqM ▸ A.j B b a a' p = a_13 →
                                          eqM ▸ B⌈(ₛidₚ), a, a', p⌉ = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_13 ∶ A_1 :=
  by
    intro n Γ' A B b a a' p hB hbB haA haA' hpId hBa hBc ihB ihbB ihaA ihaA' ihpId ihBa ihBc m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.iden_elim
    · simp [extend_expand_context]
      apply ihB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihbB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihaA'
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihpId
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihBa
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihBc
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl

theorem context_conversion_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
      (Γ ⊢ a ∶ A) →
        Γ ⊢ A ≡ B type →
          (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_3 A_1 : Tm m),
              Γ_1 ⊢ S ≡ S' type →
                Γ_1 ⊢ S type →
                  Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_3 → eqM ▸ A = A_1 → Γ_1 ⬝ S' ⊗ Δ ⊢ a_3 ∶ A_1) →
            (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A' : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → eqM ▸ B = A' → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A' type) →
              ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_5 A : Tm m),
                Γ_1 ⊢ S ≡ S' type →
                  Γ_1 ⊢ S type →
                    Γ_1 ⊢ S' type → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ a = a_5 → eqM ▸ B = A → Γ_1 ⬝ S' ⊗ Δ ⊢ a_5 ∶ A :=
  by
    intro n Γ' a A B haA hAB ihaA ihAB m l Γ Δ heqM S S' t T hSS hS hS' heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.ty_conv
    · apply ihaA
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
    · apply ihAB
      · apply hSS
      · apply hS
      · apply hS'
      repeat' rfl
