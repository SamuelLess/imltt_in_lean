import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.RulesEquality
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import IMLTT.typed.proofs.admissable.Weakening.Helpers

theorem weakening_var_eq :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x + 1 = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
    → eqM ▸ v(0) = a
    → eqM ▸ v(0) = a'
    → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A hA ihA m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases Δ with
    | start =>
      cases heqΓ
      apply_subst_eq IsEqualTerm.weak_eq (IsEqualTerm.var_eq hA) hS
    | expand Δ' S' =>
      cases heqΓ
      apply_subst_eq IsEqualTerm.var_eq
      apply ihA
      apply hS
      any_goals rfl

theorem weakening_weak_eq :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ≡ v(i) ∶ A)
    → Γ ⊢ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ v(i) = a
      → eqM ▸ v(i) = a'
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l) (A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ B = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x + 1 = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ ⬝ B = Γ_1 ⊗ Δ
    → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a
    → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a'
    → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n x Γ' A B hvvA hB ihvvA ihB m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases Δ with
    | start =>
      cases heqΓ
      apply_subst_eq IsEqualTerm.weak_eq (IsEqualTerm.weak_eq hvvA hB) hS
    | expand Δ' S' =>
      cases heqΓ
      apply_subst_eq IsEqualTerm.weak_eq
      substitution_nat_relation_lemmatas
      rw (config := {occs := .pos [1]}) [weakening_shift_id_lift]
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      · apply_subst_eq ihvvA
        try any_goals rw [←weakening_conv_var]
        apply hS
        repeat' rfl
      · apply ihB
        apply hS
        repeat' rfl

theorem weakening_unit_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
    Γ ⬝ 𝟙 ⊢ A type
    → (Γ ⊢ a ∶ A⌈⋆⌉₀)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_4 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ A⌈⋆⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_4⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indUnit ⋆ a = a_5
    → eqM ▸ a = a'
    → eqM ▸ A⌈⋆⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' A a hA haA ihA ihaA m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    apply IsEqualTerm.unit_comp
    · apply_subst_eq ihA
      rw [←weakening_unit]
      rw [←extend_expand_context_weaken_from]
      apply hS
      repeat' rfl
    · apply_subst_eq ihaA
      simp []
      rw [←weakening_tt, substitution_zero_weak_simp]
      apply hS
      repeat' rfl

theorem weakening_pi_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
    (Γ ⬝ A ⊢ b ∶ B)
    → (Γ ⊢ a ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_4 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_4⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ (λA; b)◃a = a_5
    → eqM ▸ b⌈a⌉₀ = a'
    → eqM ▸ B⌈a⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' A b B a hbB haA ihbB ihaA m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    rw [substitution_zero_weak]
    apply IsEqualTerm.pi_comp
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [extend_expand_context_weaken_from]
      apply ihbB
      apply hS
      repeat' rfl
      apply gen_ctx_leq Δ
    · apply ihaA
      apply hS
      repeat' rfl

theorem weakening_sigma_comp :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
    (Γ ⬝ ΣA;B) ⊢ C type
    → (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ b ∶ B⌈a⌉₀)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⊗ Δ
      → eqM ▸ C = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⊗ Δ
      → eqM ▸ c = a
      → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_7 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_7
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_7⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_8 A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ b = a_8
      → eqM ▸ B⌈a⌉₀ = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_8⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_9 a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indSigma B C c (a&b) = a_9
    → eqM ▸ c⌈(ₛidₚ)⋄ a⋄ b⌉ = a'
    → eqM ▸ C⌈a&b⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_9⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' a A b B C c hC hcC haA hbB ihC ihcC ihaA ihbB m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    rw [helper_weakening_sigma_elim_c]
    apply IsEqualTerm.sigma_comp
    · simp [lift_weak_n]
      rw [←weakening_sigma]
      rw [extend_expand_context_weaken_from]
      rw [lift_weaken_from]
      apply ihC
      apply hS
      repeat' rfl
      apply gen_ctx_leq Δ
    · have h := gen_ctx_leq Δ
      simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [lift_weaken_from]
      rw [extend_expand_context_weaken_from]
      rw [extend_expand_context_weaken_from]
      rw [helper_weakening_sigma_elim_C]
      apply ihcC
      apply hS
      repeat' rfl
      any_goals omega
    · apply ihaA
      apply hS
      repeat' rfl
    · apply_subst_eq ihbB
      apply hS
      repeat' rfl

theorem weakening_nat_zero_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ 𝓏 ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ z = a
      → eqM ▸ A⌈𝓏⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ s = a
      → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ 𝓏 = a
      → eqM ▸ 𝒩 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A.indNat z s 𝓏 = a
      → eqM ▸ z = a'
      → eqM ▸ A⌈𝓏⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' z A s hA hzA hsA hzNat ihA ihzA ihsA ihzNat m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    apply IsEqualTerm.nat_zero_comp
    · apply_subst_eq ihA
      rw [←extend_expand_context_weaken_from, ←weakening_nat]
      apply hS
      repeat' rfl
    · apply_subst_eq ihzA
      simp []
      rw [←weakening_nat_zero, substitution_zero_weak_simp]
      apply hS
      repeat' rfl
    · apply replaceWithEq
      rotate_right
      apply_replace_meta ihsA
      rotate_right 2
      congr 1
      try any_goals apply ihsA
      · simp []
        rw [←weakening_nat]
        rw (config := {occs := .pos [2]}) [extend_expand_context_weaken_from]
        rw [lift_weaken_from]
        rw (config := {occs := .pos [2]}) [extend_expand_context_weaken_from]
        context_info_nat_relations
        assumption
      · substitution_norm
      · rw [helper_weakkening_nat_elim_succ]
        exact gen_ctx_leq Δ
      exact hS
      repeat' rfl
    · rw [←weakening_nat]
      rw [←weakening_nat_zero]
      apply ihzNat
      apply hS
      repeat' rfl


theorem weakening_nat_succ_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ z = a
      → eqM ▸ A⌈𝓏⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ s = a
      → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ x = a
      → eqM ▸ 𝒩 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indNat z s 𝓈(x) = a
    → eqM ▸ s⌈(ₛidₚ)⋄ x⋄ A.indNat z s x⌉ = a'
    → eqM ▸ A⌈𝓈(x)⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ z x A s hA hzA hsA hxNat ihA ihzA ihsA ihxNat m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    rw [helper_weakening_sigma_elim_c]
    apply IsEqualTerm.nat_succ_comp
    · apply_subst_eq ihA
      rw [←extend_expand_context_weaken_from, ←weakening_nat]
      apply hS
      repeat' rfl
    · apply_subst_eq ihzA
      simp []
      rw [←weakening_nat_zero, substitution_zero_weak_simp]
      apply hS
      repeat' rfl
    · apply replaceWithEq
      rotate_right
      apply_replace_meta ihsA
      rotate_right 2
      congr 1
      try any_goals apply ihsA
      · simp []
        rw [←weakening_nat]
        rw (config := {occs := .pos [2]}) [extend_expand_context_weaken_from]
        rw [lift_weaken_from]
        rw (config := {occs := .pos [2]}) [extend_expand_context_weaken_from]
        context_info_nat_relations
        assumption
      · substitution_norm
      · rw [helper_weakkening_nat_elim_succ]
        exact gen_ctx_leq Δ
      exact hS
      repeat' rfl
    · rw [←weakening_nat]
      apply ihxNat
      exact hS
      repeat' rfl

theorem weakening_iden_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
    → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → (Γ ⊢ a ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⊗ Δ
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_6 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_6
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_6⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_7 a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.j B b a a (A.refl a) = a_7
    → eqM ▸ b⌈a⌉₀ = a'
    → eqM ▸ B⌈(ₛidₚ)⋄ a⋄ a⋄ A.refl a⌉ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_7⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A B b a hB hbB haA ihB ihbB ihaA m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    rw [helper_weakening_iden_elim_B]
    apply IsEqualTerm.iden_comp
    · apply use_equality_type
      apply ihB
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
      any_goals substitution_norm
    · apply use_equality_term
      apply ihbB
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
    · apply ihaA
      apply hS
      repeat' rfl

theorem weakening_unit_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ ⋆ = a
    → eqM ▸ ⋆ = a'
    → eqM ▸ 𝟙 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.unit_intro_eq
    apply ihiC
    · exact hS
    repeat' rfl

theorem weakening_unit_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
    Γ ⬝ 𝟙 ⊢ A ≡ A' type
    → (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀)
    → (Γ ⊢ b ≡ b' ∶ 𝟙)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_5
      → eqM ▸ a' = a'_1
      → eqM ▸ A⌈⋆⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ b' = a'
      → eqM ▸ 𝟙 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_7 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A.indUnit b a = a_7
      → eqM ▸ A'.indUnit b' a' = a'_1
      → eqM ▸ A⌈b⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_7⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihbb1 m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    apply IsEqualTerm.unit_elim_eq
    · apply_subst_eq ihAA
      rw [←weakening_unit, ←extend_expand_context_weaken_from]
      apply hS
      repeat' rfl
    · apply_subst_eq ihaaA
      simp []
      rw [←weakening_tt, substitution_zero_weak_simp]
      apply hS
      repeat' rfl
    · rw [←weakening_unit]
      apply ihbb1
      apply hS
      repeat' rfl

theorem weakening_empty_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
    Γ ⬝ 𝟘 ⊢ A ≡ A' type
    → (Γ ⊢ b ≡ b' ∶ 𝟘)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ b' = a'
      → eqM ▸ 𝟘 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indEmpty b = a
    → eqM ▸ A'.indEmpty b' = a'
    → eqM ▸ A⌈b⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' A A' b b' hAA hbb0 ihAA ihbb0 m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    apply IsEqualTerm.empty_elim_eq
    · rw [←weakening_empty]
      rw [extend_expand_context_weaken_from]
      apply use_equality_type_eq
      apply ihAA
      apply hS
      rw [extend_expand_context]
      substitution_step_meta
      substitution_step_meta
      substitution_step_meta
    · rw [←weakening_empty]
      apply ihbb0
      apply hS
      repeat' rfl

theorem weakening_pi_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B)
    → Γ ⊢ A ≡ A' type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ b' = a'
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (eqM ▸ λA; b) = a
      → (eqM ▸ λA'; b') = a'
      → (eqM ▸ ΠA;B) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' A A' b b' B hbbB hAA ihbbB ihAA m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.pi_intro_eq
    · apply_subst_eq ihbbB
      rw [extend_expand_context_weaken_from]
      apply hS
      repeat' rfl
    · apply ihAA
      apply hS
      repeat' rfl

theorem weakening_pi_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
    (Γ ⊢ f ≡ f' ∶ ΠA;B)
    → (Γ ⊢ a ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ f = a
      → eqM ▸ f' = a'
      → (eqM ▸ ΠA;B) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_4 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ a' = a'_1
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_4⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 a'_1 A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ f◃a = a_5
    → eqM ▸ f'◃a' = a'_1
    → eqM ▸ B⌈a⌉₀ = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' f f' A B a a' hffPi haaA ihffPi ihaaA m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    apply IsEqualTerm.pi_elim_eq
    · rw [←weakening_pi]
      apply ihffPi
      apply hS
      repeat' rfl
    · apply ihaaA
      apply hS
      repeat' rfl

theorem weakening_sigma_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ≡ a' ∶ A)
    → (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀)
    → Γ ⬝ A ⊢ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_4 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ a' = a'_1
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_4⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ b = a_5
      → eqM ▸ b' = a'
      → eqM ▸ B⌈a⌉₀ = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_7 a'_1 A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ a&b = a_7
    → eqM ▸ a'&b' = a'_1
    → (eqM ▸ ΣA;B) = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_7⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' a a' A b b' B haaA hbbB hB ihaaA ihbbB ihB m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.sigma_intro_eq
    · apply ihaaA
      apply hS
      repeat' rfl
    · apply_subst_eq ihbbB
      apply hS
      repeat' rfl
    · apply_subst_eq ihB
      rw [extend_expand_context_weaken_from]
      apply hS
      repeat' rfl

theorem weakening_sigma_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n}
    {C C' : Tm (n + 1)} {c c' : Tm (n + 1 + 1)},
    (Γ ⬝ ΣA;B) ⊢ C ≡ C' type
    → (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
    → Γ ⊢ A ≡ A' type
    → Γ ⬝ A ⊢ B ≡ B' type
    → (Γ ⊢ p ≡ p' ∶ ΣA;B)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S type
      → (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⊗ Δ
      → eqM ▸ C = A_1
      → eqM ▸ C' = A'
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⊗ Δ
      → eqM ▸ c = a
      → eqM ▸ c' = a'
      → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = A_1
      → eqM ▸ B' = A'
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ p = a
      → eqM ▸ p' = a'
      → (eqM ▸ ΣA;B) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indSigma B C c p = a
    → eqM ▸ A'.indSigma B' C' c' p' = a'
    → eqM ▸ C⌈p⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A B A' B' p p' C C' c c' hCC hccC hAA hBB hppSi ihCC ihccC ihAA ihBB ihppSi
      m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    apply IsEqualTerm.sigma_elim_eq
    · have h := gen_ctx_leq Δ
      simp [lift_weak_n]
      rw [lift_weaken_from]
      rw (config := {occs := .pos [1]}) [←lift_weaken_from]
      rw [←weakening_sigma]
      rw [extend_expand_context_weaken_from]
      apply ihCC
      apply hS
      repeat' rfl
      any_goals omega
    · apply use_equality_term_eq
      apply ihccC
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
      any_goals substitution_step_meta
      substitution_norm
    · apply ihAA
      apply hS
      repeat' rfl
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [extend_expand_context_weaken_from]
      apply ihBB
      repeat' rfl
      apply hS
      apply gen_ctx_leq Δ
    · simp [lift_weak_n]
      rw [←weakening_sigma]
      apply ihppSi
      apply hS
      repeat' rfl

theorem weakening_nat_zero_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝓏 = a
    → eqM ▸ 𝓏 = a'
    → eqM ▸ 𝒩 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_zero_intro_eq
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_nat_succ_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {x x' : Tm n},
    (Γ ⊢ x ≡ x' ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ x = a
      → eqM ▸ x' = a'
      → eqM ▸ 𝒩 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝓈(x) = a
    → eqM ▸ 𝓈(x') = a'
    → eqM ▸ 𝒩 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' x x' hxxNat ihxxNat m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_succ_intro_eq
    rw [←weakening_nat]
    apply ihxxNat
    apply hS
    repeat' rfl

theorem weakening_nat_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {z z' x x' : Tm n} {A A' : Tm (n + 1)} {s s' : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A ≡ A' type
    → (Γ ⊢ z ≡ z' ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ≡ s' ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ≡ x' ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ z = a
      → eqM ▸ z' = a'
      → eqM ▸ A⌈𝓏⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ s = a
      → eqM ▸ s' = a'
      → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ x = a
      → eqM ▸ x' = a'
      → eqM ▸ 𝒩 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indNat z s x = a
    → eqM ▸ A'.indNat z' s' x' = a'
    → eqM ▸ A⌈x⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ z z' x x' A A' s s' hAA hzzA hssA hxxNat ihAA ihzzA ihssA ihxxNat
      m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_weak]
    apply IsEqualTerm.nat_elim_eq
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [←weakening_nat]
      rw [extend_expand_context_weaken_from]
      apply ihAA
      repeat' rfl
      apply hS
      apply gen_ctx_leq Δ
    · apply use_equality_term_eq
      apply ihzzA
      apply hS
      any_goals substitution_step_meta
      any_goals substitution_norm
    · apply use_equality_term_eq
      apply ihssA
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
      substitution_norm
    · rw [←weakening_nat]
      apply ihxxNat
      apply hS
      repeat' rfl

theorem weakening_iden_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
    Γ ⊢ A ≡ A' type
    → (Γ ⊢ a ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_4 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ a' = a'_1
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_4⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A.refl a = a_5
      → eqM ▸ A'.refl a' = a'_1
      → (eqM ▸ a ≃[A] a) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A A' a a' hAA haaA ihAA ihaaA m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.iden_intro_eq
    · apply ihAA
      apply hS
      repeat' rfl
    · apply ihaaA
      apply hS
      repeat' rfl

theorem weakening_iden_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' : Tm (n + 1)}
    {a₁ a₃ A' a₂ a₄ p p' : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type
    → (Γ ⬝ A ⊢ b ≡ b' ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → Γ ⊢ A ≡ A' type
    → (Γ ⊢ a₁ ≡ a₂ ∶ A)
    → (Γ ⊢ a₃ ≡ a₄ ∶ A')
    → (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 + 1 = m) (S : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S type
      → (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⊗ Δ
      → eqM ▸ B = A_1
      → eqM ▸ B' = A'
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ b' = a'
      → eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ A' = A'_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a₁ = a
      → eqM ▸ a₂ = a'
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a₃ = a
      → eqM ▸ a₄ = a'
      → eqM ▸ A' = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ p = a
      → eqM ▸ p' = a'
      → (eqM ▸ a₁ ≃[A] a₃) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.j B b a₁ a₃ p = a
    → eqM ▸ A'.j B' b' a₂ a₄ p' = a'
    → eqM ▸ B⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hAA haaA haaA' hppId ihBB ihbbB ihAA ihaaA ihaaA' ihppId
      m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [helper_weakening_iden_elim_B]
    apply IsEqualTerm.iden_elim_eq
    · apply use_equality_type_eq
      apply ihBB
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
      any_goals substitution_norm
    · apply use_equality_term_eq
      apply ihbbB
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
    · apply ihAA
      apply hS
      repeat' rfl
    · apply ihaaA
      apply hS
      repeat' rfl
    · apply ihaaA'
      apply hS
      repeat' rfl
    · rw [←weakening_iden]
      apply ihppId
      apply hS
      repeat' rfl

theorem weakening_univ_unit_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝟙 = a
    → eqM ▸ 𝟙 = a'
    → eqM ▸ 𝒰 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_unit_eq
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_univ_empty_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ 𝟘 = a
      → eqM ▸ 𝟘 = a'
      → eqM ▸ 𝒰 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_empty_eq
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_univ_pi_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ A' = a'
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = a
      → eqM ▸ B' = a'
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ ΠA;B) = a
    → (eqM ▸ ΠA';B') = a'
    → eqM ▸ 𝒰 = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_pi_eq
    · rw [←weakening_univ]
      apply ihAAU
      apply hS
      repeat' rfl
    · apply_subst_eq ihBBU
      rw (config := {occs := .pos [1]}) [extend_expand_context_weaken_from]
      rw [←weakening_univ]
      apply hS
      rw [extend_expand_context]
      repeat' rfl

theorem weakening_univ_sigma_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ A' = a'
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = a
      → eqM ▸ B' = a'
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ ΣA;B) = a
    → (eqM ▸ ΣA';B') = a'
    → eqM ▸ 𝒰 = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_sigma_eq
    · rw [←weakening_univ]
      apply ihAAU
      apply hS
      repeat' rfl
    · apply_subst_eq ihBBU
      rw (config := {occs := .pos [1]}) [extend_expand_context_weaken_from]
      rw [←weakening_univ]
      apply hS
      rw [extend_expand_context]
      repeat' rfl

theorem weakening_univ_nat_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ 𝒩 = a
      → eqM ▸ 𝒩 = a'
      → eqM ▸ 𝒰 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_nat_eq
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_univ_iden_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⊢ a₁ ≡ a₂ ∶ A)
    → (Γ ⊢ a₃ ≡ a₄ ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ A' = a'
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a₁ = a
      → eqM ▸ a₂ = a'
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a₃ = a
      → eqM ▸ a₄ = a'
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ a₁ ≃[A] a₃) = a
    → (eqM ▸ a₂ ≃[A'] a₄) = a'
    → eqM ▸ 𝒰 = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' ihAAU ihaaA ihaaA' m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_iden_eq
    · rw [←weakening_univ]
      apply ihAAU
      apply hS
      repeat' rfl
    · apply ihaaA
      apply hS
      repeat' rfl
    · apply ihaaA'
      apply hS
      repeat' rfl

theorem weakening_ty_conv_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
    (Γ ⊢ a ≡ b ∶ A)
    → Γ ⊢ A ≡ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_3 a' A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_3
      → eqM ▸ b = a'
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_3⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ B = A'
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 a' A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ a = a_5
    → eqM ▸ b = a'
    → eqM ▸ B = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' a b A B habA hAB ihabA ihAB m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.ty_conv_eq
    · apply ihabA
      apply hS
      repeat' rfl
    · apply ihAB
      apply hS
      repeat' rfl

theorem weakening_term_symm :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A : Tm n},
    (Γ ⊢ a ≡ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_1 a'_1 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_1
      → eqM ▸ a' = a'_1
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_1⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_2 a'_1 A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ a' = a_2
    → eqM ▸ a = a'_1
    → eqM ▸ A = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_2⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ a a' A haaA ihaaA m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.term_symm
    apply ihaaA
    apply hS
    repeat' rfl

theorem weakening_term_trans :
    ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
    (Γ ⊢ a ≡ b ∶ T)
    → (Γ ⊢ b ≡ c ∶ T)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_1 a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_1
      → eqM ▸ b = a'
      → eqM ▸ T = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_1⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ c = a'
      → eqM ▸ T = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_3 a' A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_3
      → eqM ▸ c = a'
      → eqM ▸ T = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_3⌊↑₁m↬l⌋ ≡ a'⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ T a b c habT hbcT ihabT ihbcT m l Γ Δ heqM S t t' T hS heqΓ heqt heqt' heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.term_trans
    · apply ihabT
      apply hS
      repeat' rfl
    · apply ihbcT
      apply hS
      repeat' rfl
