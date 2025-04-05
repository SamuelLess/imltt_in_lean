import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.DefeqRefl
import IMLTT.typed.proofs.admissable.weakening.WeakeningGeneral

import IMLTT.typed.proofs.admissable.weaksubstitution.Helpers
import IMLTT.typed.proofs.admissable.substitution.Helpers

theorem weak_substitution_var_eq :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (s : Tm (l + 1)) {S : Tm l}
          (A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (s : Tm (l + 1)) (S : Tm l)
          (a a' A_1 : Tm m),
          eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ v(0) = a →
              eqM ▸ v(0) = a' →
                eqM ▸ A⌊↑ₚidₚ⌋ = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A hA ihA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases n with
    | zero =>
      simp [substitute]
      simp [n_substitution_shift]
      simp [substitute_var]
      simp [substitution_comp_σρ]
      simp [comp_substitute_weaken]
      cases Δ with
      | start =>
        cases heqΓ
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [substitution_conv_shift_id_conv]
        apply defeq_refl_term hsS
      | expand Δ' T =>
        have h1 := gen_ctx_leq Δ'
        omega
    | succ n' =>
      cases Δ with
      | start =>
        cases heqΓ
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        rw [n_substitution_shift_zero]
        rw [substitution_comp_σρ]
        simp [comp_substitute_weaken]
        simp [substitute]
        simp [substitute_var]
        rw [substitution_conv_shift_id_conv]
        apply defeq_refl_term hsS
      | expand Δ' T =>
        cases heqΓ
        simp [substitute]
        rw [←lift_n_substitution_shift]
        simp [substitution_shift_id_lift]
        simp [←extend_expand_context_n_substitution_shift]
        rw (config := {occs := .pos [2]}) [n_substitution_shift]
        rw (config := {occs := .pos [2]}) [n_substitution_shift]
        simp_all
        split
        case isTrue hlt =>
          simp [substitute_var]
          apply IsEqualTerm.var_eq
          apply ihA
          · rfl
          · apply hsS
          · rfl
        case isFalse hnlt =>
          simp [substitute_var]
          apply IsEqualTerm.var_eq
          apply ihA
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_weak_eq :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ≡ v(i) ∶ A) →
      Γ ⊢ B type →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (s : Tm (l + 1)) (S : Tm l)
            (a a' A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ v(i) = a →
                eqM ▸ v(i) = a' →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) (s : Tm (l + 1)) {S : Tm l}
              (A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = A → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) (s : Tm (l + 1))
              (S : Tm l) (a a' A_1 : Tm m),
              eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ v(i)⌊↑ₚidₚ⌋ = a →
                  eqM ▸ v(i)⌊↑ₚidₚ⌋ = a' →
                    eqM ▸ A⌊↑ₚidₚ⌋ = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n x Γ' A B hvA hB ihvA ihB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases n with
    | zero =>
      cases Δ with
      | start =>
        cases heqΓ
        simp [n_substitution_shift]
        simp [substitution_comp_σρ]
        simp [comp_substitute_weaken]
        rw [empty_extend_expand_context_n_substitution_shift (Γ := Γ' ⬝ B)]
        rw [empty_expand_context]
        simp [substitution_conv_shift_id_conv]
        apply IsEqualTerm.weak_eq
        · apply hvA
        · apply hB
      | expand Δ' T =>
        have h1 := gen_ctx_leq Δ'
        omega
    | succ n' =>
      cases Δ with
      | start =>
        cases heqΓ
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        rw [n_substitution_shift_zero]
        simp [substitution_comp_σρ]
        simp [comp_substitute_weaken]
        simp [substitution_conv_shift_id_conv]
        apply IsEqualTerm.weak_eq
        · apply hvA
        · apply hB
      | expand Δ' T =>
        cases heqΓ
        rw [←lift_n_substitution_shift]
        simp [substitution_shift_id_lift]
        simp [←extend_expand_context_n_substitution_shift]
        apply weakening_term_eq
        · apply ihvA
          · rfl
          · rfl
          · rfl
          · rfl
          · apply hsS
          · rfl
        · apply ihB
          · rfl
          · rfl
          · apply hsS
          · rfl
        · have h := gen_ctx_leq Δ'
          omega

theorem weak_substitution_unit_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
    Γ ⬝ 𝟙 ⊢ A type →
      (Γ ⊢ a ∶ A⌈⋆⌉₀) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
            {S : Tm l} (A_1 : Tm m),
            eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_4 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_4 →
                  eqM ▸ A⌈⋆⌉₀ = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_4⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_5 a' A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A.indUnit ⋆ a = a_5 →
                  eqM ▸ a = a' →
                    eqM ▸ A⌈⋆⌉₀ = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ A a hA haA ihA ihaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    simp [substitution_zero_lift]
    apply IsEqualTerm.unit_comp
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      rw [←substitution_unit]
      rw [extend_expand_context_n_substitution_shift]
      apply ihA
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_tt]
      rw [←substitution_zero_lift]
      apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_pi_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
    (Γ ⬝ A ⊢ b ∶ B) →
      (Γ ⊢ a ∶ A) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
            (S : Tm l) (a A_1 : Tm m),
            eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ b = a →
                eqM ▸ B = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_4 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_4 →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_4⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_5 a' A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ (λA; b)◃a = a_5 →
                  eqM ▸ b⌈a⌉₀ = a' →
                    eqM ▸ B⌈a⌉₀ = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A b B a hbB haA ihbB ihaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_zero_lift]
    apply IsEqualTerm.pi_comp
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihbB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_sigma_comp :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
  (Γ ⊢ a ∶ A) →
    (Γ ⊢ b ∶ B⌈a⌉₀) →
      (Γ ⬝ ΣA;B) ⊢ C type →
        (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
              (S : Tm l) (a_5 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_5 →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (a_6 A : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ b = a_6 →
                    eqM ▸ B⌈a⌉₀ = A →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_6⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                  {S : Tm l} (A_1 : Tm m),
                  (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ C = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
                (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m)
                    (s : Tm (l + 1)) (S : Tm l) (a A_1 : Tm m),
                    eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ c = a →
                        eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 →
                          (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                  ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                    (S : Tm l) (a_9 a' A_1 : Tm m),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A.indSigma B C c (a&b) = a_9 →
                        eqM ▸ c⌈(ₛidₚ), a, b⌉ = a' →
                          eqM ▸ C⌈a&b⌉₀ = A_1 →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_9⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' a A b B C c haA hbB hC hcC ihaA ihbB ihC ihcC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_zero_lift]
    rw [subst_subst_sigma_c]
    apply IsEqualTerm.sigma_comp
    · apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_zero_lift]
      apply ihbB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihC
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [subst_subst_sigma_C]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihcC
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_nat_zero_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type →
      (Γ ⊢ z ∶ A⌈𝓏⌉₀) →
        (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
          (Γ ⊢ 𝓏 ∶ 𝒩) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                {S : Tm l} (A_1 : Tm m),
                eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ z = a →
                      eqM ▸ A⌈𝓏⌉₀ = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m)
                    (s_1 : Tm (l + 1)) (S : Tm l) (a A_1 : Tm m),
                    eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ s = a →
                        eqM ▸ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1 →
                          (Γ_1 ⬝ S ⊢ s_1 ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s_1↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s_1↑/ₙleq⌉ ∶ A_1⌈s_1↑/ₙleq⌉) →
                  (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                      (S : Tm l) (a A : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ 𝓏 = a →
                          eqM ▸ 𝒩 = A →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
                    ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s_1 : Tm (l + 1))
                      (S : Tm l) (a a' A_1 : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ A.indNat z s 𝓏 = a →
                          eqM ▸ z = a' →
                            eqM ▸ A⌈𝓏⌉₀ = A_1 →
                              (Γ_1 ⬝ S ⊢ s_1 ∶ S⌊↑ₚidₚ⌋) →
                                Γ_1 ⬝ S ⊗ ⌈s_1↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s_1↑/ₙleq⌉ ≡ a'⌈s_1↑/ₙleq⌉ ∶ A_1⌈s_1↑/ₙleq⌉ :=
  by
    intro n Γ' z A s hA hzA hsA hzNat ihA ihzA ihsA ihzNat m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_zero_lift]
    apply IsEqualTerm.nat_zero_comp
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [←substitution_nat]
      rw [extend_expand_context_n_substitution_shift]
      apply ihA
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_var_zero]
      rw [←substitution_zero_lift]
      apply ihzA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←helper_weak_subst_nat_elim (A := A)]
      rw [←substitution_nat]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihsA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
      any_goals omega
    · rw [←substitution_nat]
      rw [←substitution_var_zero]
      apply ihzNat
      · apply hleq
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_nat_succ_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type →
      (Γ ⊢ z ∶ A⌈𝓏⌉₀) →
        (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
          (Γ ⊢ x ∶ 𝒩) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                {S : Tm l} (A_1 : Tm m),
                eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ z = a →
                      eqM ▸ A⌈𝓏⌉₀ = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m)
                    (s_1 : Tm (l + 1)) (S : Tm l) (a A_1 : Tm m),
                    eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ s = a →
                        eqM ▸ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1 →
                          (Γ_1 ⬝ S ⊢ s_1 ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s_1↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s_1↑/ₙleq⌉ ∶ A_1⌈s_1↑/ₙleq⌉) →
                  (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                      (S : Tm l) (a A : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ x = a →
                          eqM ▸ 𝒩 = A →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
                    ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s_1 : Tm (l + 1))
                      (S : Tm l) (a a' A_1 : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ A.indNat z s 𝓈(x) = a →
                          eqM ▸ s⌈(ₛidₚ), x, A.indNat z s x⌉ = a' →
                            eqM ▸ A⌈𝓈(x)⌉₀ = A_1 →
                              (Γ_1 ⬝ S ⊢ s_1 ∶ S⌊↑ₚidₚ⌋) →
                                Γ_1 ⬝ S ⊗ ⌈s_1↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s_1↑/ₙleq⌉ ≡ a'⌈s_1↑/ₙleq⌉ ∶ A_1⌈s_1↑/ₙleq⌉ :=
  by
    intro n Γ' z x A s hA hzA hsA hsNat ihA ihzA ihsA ihsNat m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    rw [subst_subst_sigma_c]
    apply IsEqualTerm.nat_succ_comp
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [←substitution_nat]
      rw [extend_expand_context_n_substitution_shift]
      apply ihA
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_var_zero]
      rw [←substitution_zero_lift]
      apply ihzA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←helper_weak_subst_nat_elim]
      rw [←substitution_nat]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihsA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
      any_goals omega
    · rw [←substitution_nat]
      apply ihsNat
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_iden_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
    (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉) →
      (Γ ⊢ a ∶ A) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 + 1 = m)
              (s : Tm (l + 1)) {S : Tm l} (A_1 : Tm m),
              (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                (S : Tm l) (a A_1 : Tm m),
                eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ b = a →
                    eqM ▸ B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a_7 A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a = a_7 →
                      eqM ▸ A = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_7⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                  ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                    (S : Tm l) (a_9 a' A_1 : Tm m),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A.j B b a a (A.refl a) = a_9 →
                        eqM ▸ b⌈a⌉₀ = a' →
                          eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_9⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A B b a hB hbB haA ihB ihbB ihaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    rw [subst_subst_iden_elim]
    simp [substitution_zero_lift]
    apply IsEqualTerm.iden_comp
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      simp [←substitution_shift_id_lift]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      simp_all
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_subst_iden_propagate_subst]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihB
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_shift_id_lift]
      rw [subst_subst_iden_refl]
      rw [extend_expand_context_n_substitution_shift]
      simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      apply ihbB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_unit_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
        (a a' A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ ⋆ = a →
            eqM ▸ ⋆ = a' →
              eqM ▸ 𝟙 = A →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.unit_intro_eq
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_unit_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
    Γ ⬝ 𝟙 ⊢ A ≡ A' type →
      (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀) →
        (Γ ⊢ b ≡ b' ∶ 𝟙) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              (S : Tm l) (A_1 A'_1 : Tm m),
              eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ A' = A'_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (a_5 a'_1 A_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a = a_5 →
                    eqM ▸ a' = a'_1 →
                      eqM ▸ A⌈⋆⌉₀ = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a a' A : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ b = a →
                      eqM ▸ b' = a' →
                        eqM ▸ 𝟙 = A →
                          (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
                ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a_7 a'_1 A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ A.indUnit b a = a_7 →
                      eqM ▸ A'.indUnit b' a' = a'_1 →
                        eqM ▸ A⌈b⌉₀ = A_1 →
                          (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_7⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihbb1 m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    simp [substitution_zero_lift]
    apply IsEqualTerm.unit_elim_eq
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      rw [←substitution_unit]
      rw [extend_expand_context_n_substitution_shift]
      apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_tt]
      rw [←substitution_zero_lift]
      apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_unit]
      apply ihbb1
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_empty_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
    Γ ⬝ 𝟘 ⊢ A ≡ A' type →
      (Γ ⊢ b ≡ b' ∶ 𝟘) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
            (S : Tm l) (A_1 A'_1 : Tm m),
            eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 →
                eqM ▸ A' = A'_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a a' A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ b = a →
                  eqM ▸ b' = a' →
                    eqM ▸ 𝟘 = A →
                       (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a a' A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A.indEmpty b = a →
                  eqM ▸ A'.indEmpty b' = a' →
                    eqM ▸ A⌈b⌉₀ = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A A' b b' hAA hbb0 ihAA ihbb0 m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    simp [substitution_zero_lift]
    apply IsEqualTerm.empty_elim_eq
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      rw [←substitution_empty]
      rw [extend_expand_context_n_substitution_shift]
      apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_empty]
      apply ihbb0
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_pi_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B) →
      Γ ⊢ A ≡ A' type →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
            (S : Tm l) (a a' A_1 : Tm m),
            eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ b = a →
                eqM ▸ b' = a' →
                  eqM ▸ B = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (A_1 A'_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ A' = A'_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a a' A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ λA; b) = a →
                  (eqM ▸ λA'; b') = a' →
                    (eqM ▸ ΠA;B) = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A A' b b' B hbbB hPiPi ihbbB ihPiPi m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.pi_intro_eq
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihbbB
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihPiPi
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_pi_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
    (Γ ⊢ f ≡ f' ∶ ΠA;B) →
      (Γ ⊢ a ≡ a' ∶ A) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a a' A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ f = a →
                eqM ▸ f' = a' →
                  (eqM ▸ ΠA;B) = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_4 a'_1 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_4 →
                  eqM ▸ a' = a'_1 →
                    eqM ▸ A = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_4⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_5 a'_1 A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ f◃a = a_5 →
                  eqM ▸ f'◃a' = a'_1 →
                    eqM ▸ B⌈a⌉₀ = A →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' f f' A B a a' hffPi haaA ihffPi ihaaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_zero_lift]
    apply IsEqualTerm.pi_elim_eq
    · rw [←substitution_pi]
      apply ihffPi
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_sigma_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ≡ a' ∶ A) →
      (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀) →
        Γ ⬝ A ⊢ B type →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_4 a'_1 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_4 →
                  eqM ▸ a' = a'_1 →
                    eqM ▸ A = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_4⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (a_5 a' A : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ b = a_5 →
                    eqM ▸ b' = a' →
                      eqM ▸ B⌈a⌉₀ = A →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                  {S : Tm l} (A_1 : Tm m),
                  eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ B = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ type) →
                ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a_7 a'_1 A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a&b = a_7 →
                      eqM ▸ a'&b' = a'_1 →
                        (eqM ▸ ΣA;B) = A_1 →
                          (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_7⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' a a' A b b' B haaA hbbB hB ihaaA ihbbB ihB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.sigma_intro_eq
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      simp [←substitution_zero_lift]
      apply ihbbB
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihB
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_sigma_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)}
  {c c' : Tm (n + 1 + 1)},
  Γ ⊢ A ≡ A' type →
    Γ ⬝ A ⊢ B ≡ B' type →
      (Γ ⊢ p ≡ p' ∶ ΣA;B) →
        (Γ ⬝ ΣA;B) ⊢ C ≡ C' type →
          (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (A_1 A'_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 →
                    eqM ▸ A' = A'_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                  (S : Tm l) (A_1 A' : Tm m),
                  eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ B = A_1 →
                      eqM ▸ B' = A' →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
                (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                    (S : Tm l) (a a' A_1 : Tm m),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ p = a →
                        eqM ▸ p' = a' →
                          (eqM ▸ ΣA;B) = A_1 →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                  (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m)
                      (s : Tm (l + 1)) (S : Tm l) (A_1 A' : Tm m),
                      (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ C = A_1 →
                          eqM ▸ C' = A' →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
                    (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m)
                        (s : Tm (l + 1)) (S : Tm l) (a a' A_1 : Tm m),
                        eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ c = a →
                            eqM ▸ c' = a' →
                              eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 →
                                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                        (s : Tm (l + 1)) (S : Tm l) (a a' A_1 : Tm m),
                        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ A.indSigma B C c p = a →
                            eqM ▸ A'.indSigma B' C' c' p' = a' →
                              eqM ▸ C⌈p⌉₀ = A_1 →
                                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A B A' B' p p' C C' c c' hAA hBB hppSi hCC hccC ihAA ihBB ihppSi ihCC ihccC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_zero_lift]
    apply IsEqualTerm.sigma_elim_eq
    · apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihBB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      apply ihppSi
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihCC
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [subst_subst_sigma_C]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihccC
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_nat_zero_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
        (a a' A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝓏 = a →
            eqM ▸ 𝓏 = a' →
              eqM ▸ 𝒩 = A →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_zero_intro_eq
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_nat_succ_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {x x' : Tm n},
    (Γ ⊢ x ≡ x' ∶ 𝒩) →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a a' A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ x = a →
              eqM ▸ x' = a' →
                eqM ▸ 𝒩 = A →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a a' A : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ 𝓈(x) = a →
              eqM ▸ 𝓈(x') = a' →
                eqM ▸ 𝒩 = A →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' x x' hxxNat ihxxNat m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.nat_succ_intro_eq
    rw [←substitution_nat]
    apply ihxxNat
    · rfl
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem weak_substitution_nat_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {z z' x x' : Tm n} {A A' : Tm (n + 1)} {s s' : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A ≡ A' type →
      (Γ ⊢ z ≡ z' ∶ A⌈𝓏⌉₀) →
        (Γ ⬝ 𝒩 ⬝ A ⊢ s ≡ s' ∶ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
          (Γ ⊢ x ≡ x' ∶ 𝒩) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
                (S : Tm l) (A_1 A'_1 : Tm m),
                eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ A = A_1 →
                    eqM ▸ A' = A'_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a a' A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ z = a →
                      eqM ▸ z' = a' →
                        eqM ▸ A⌈𝓏⌉₀ = A_1 →
                          (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 = m)
                    (s_1 : Tm (l + 1)) (S : Tm l) (a a' A_1 : Tm m),
                    eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ s = a →
                        eqM ▸ s' = a' →
                          eqM ▸ A⌈(ₛ↑ₚidₚ), 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1 →
                            (Γ_1 ⬝ S ⊢ s_1 ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s_1↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s_1↑/ₙleq⌉ ≡ a'⌈s_1↑/ₙleq⌉ ∶ A_1⌈s_1↑/ₙleq⌉) →
                  (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                      (S : Tm l) (a a' A : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ x = a →
                          eqM ▸ x' = a' →
                            eqM ▸ 𝒩 = A →
                              (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
                    ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s_1 : Tm (l + 1))
                      (S : Tm l) (a a' A_1 : Tm m),
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ A.indNat z s x = a →
                          eqM ▸ A'.indNat z' s' x' = a' →
                            eqM ▸ A⌈x⌉₀ = A_1 →
                              (Γ_1 ⬝ S ⊢ s_1 ∶ S⌊↑ₚidₚ⌋) →
                                Γ_1 ⬝ S ⊗ ⌈s_1↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s_1↑/ₙleq⌉ ≡ a'⌈s_1↑/ₙleq⌉ ∶ A_1⌈s_1↑/ₙleq⌉ :=
  by
    intro n Γ' z z' x x' A A' s s' hAA hzzA hssA hxxNat ihAA ihzzA ihssA ihxxNat m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    rw [substitution_zero_lift]
    apply IsEqualTerm.nat_elim_eq
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      rw [←substitution_nat]
      rw [extend_expand_context_n_substitution_shift]
      apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_var_zero]
      rw [←substitution_zero_lift]
      apply ihzzA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_nat]
      rw [extend_expand_context_n_substitution_shift]
      simp [lift_subst_n]
      rw [←helper_weak_subst_nat_elim]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihssA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
      apply hleq
    · rw [←substitution_nat]
      apply ihxxNat
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_iden_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
    Γ ⊢ A ≡ A' type →
      (Γ ⊢ a ≡ a' ∶ A) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (A_1 A'_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = A_1 →
                eqM ▸ A' = A'_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_4 a'_1 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_4 →
                  eqM ▸ a' = a'_1 →
                    eqM ▸ A = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_4⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_5 a'_1 A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A.refl a = a_5 →
                  eqM ▸ A'.refl a' = a'_1 →
                    (eqM ▸ a ≃[A] a) = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A A' a a' hAA haaA ihAA ihaaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.iden_intro_eq
    · apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_iden_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' : Tm (n + 1)} {a₁ a₃ A' a₂ a₄ p p' : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type →
    (Γ ⬝ A ⊢ b ≡ b' ∶ B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉) →
      Γ ⊢ A ≡ A' type →
        (Γ ⊢ a₁ ≡ a₂ ∶ A) →
          (Γ ⊢ a₃ ≡ a₄ ∶ A') →
            (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃) →
                  (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 + 1 + 1 = m)
                      (s : Tm (l + 1)) (S : Tm l) (A_1 A' : Tm m),
                      (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ B = A_1 →
                          eqM ▸ B' = A' →
                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
                    (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m)
                        (s : Tm (l + 1)) (S : Tm l) (a a' A_1 : Tm m),
                        eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ b = a →
                            eqM ▸ b' = a' →
                              eqM ▸ B⌈(ₛidₚ), v(0), (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1 →
                                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                          (s : Tm (l + 1)) (S : Tm l) (A_1 A'_1 : Tm m),
                          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                            eqM ▸ A = A_1 →
                              eqM ▸ A' = A'_1 →
                                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'_1⌈s↑/ₙleq⌉ type) →
                        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                            (s : Tm (l + 1)) (S : Tm l) (a a' A_1 : Tm m),
                            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                              eqM ▸ a₁ = a →
                                eqM ▸ a₂ = a' →
                                  eqM ▸ A = A_1 →
                                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶
                                        A_1⌈s↑/ₙleq⌉) →
                          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                              (s : Tm (l + 1)) (S : Tm l) (a a' A : Tm m),
                              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                eqM ▸ a₃ = a →
                                  eqM ▸ a₄ = a' →
                                    eqM ▸ A' = A →
                                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶
                                          A⌈s↑/ₙleq⌉) →
                            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                                (s : Tm (l + 1)) (S : Tm l) (a a' A_1 : Tm m),
                                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                  eqM ▸ p = a →
                                    eqM ▸ p' = a' →
                                      (eqM ▸ a₁ ≃[A] a₃) = A_1 →
                                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶
                                            A_1⌈s↑/ₙleq⌉) →
                                  ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m)
                                    (s : Tm (l + 1)) (S : Tm l) (a a' A_1 : Tm m),
                                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                      eqM ▸ A.j B b a₁ a₃ p = a →
                                        eqM ▸ A'.j B' b' a₂ a₄ p' = a' →
                                          eqM ▸ B⌈(ₛidₚ), a₁, a₃, p⌉ = A_1 →
                                            (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                                              Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶
                                                A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hAA haaA haaA' hppId ihBB ihbbB ihAA ihaaA ihaaA' ihppId
    intro m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    rw [subst_subst_iden_elim]
    apply IsEqualTerm.iden_elim_eq
    · simp [lift_subst_n]
      simp [lift_n_substitution_shift]
      simp [←substitution_shift_id_lift]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      simp_all
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_subst_iden_propagate_subst]
      simp [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      apply ihBB
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_shift_id_lift]
      rw [subst_subst_iden_refl]
      rw [extend_expand_context_n_substitution_shift]
      simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      apply ihbbB
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihAA
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA'
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_iden]
      apply ihppId
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_univ_unit_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
        (a a' A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝟙 = a →
            eqM ▸ 𝟙 = a' →
              eqM ▸ 𝒰 = A →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_unit_eq
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_univ_empty_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
        (a a' A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝟘 = a →
            eqM ▸ 𝟘 = a' →
              eqM ▸ 𝒰 = A →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_empty_eq
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_univ_pi_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a a' A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = a →
                eqM ▸ A' = a' →
                  eqM ▸ 𝒰 = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              (S : Tm l) (a a' A_1 : Tm m),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = a →
                  eqM ▸ B' = a' →
                    eqM ▸ 𝒰 = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a a' A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ ΠA;B) = a →
                  (eqM ▸ ΠA';B') = a' →
                    eqM ▸ 𝒰 = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.univ_pi_eq
    · rw [←substitution_univ]
      apply ihAAU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [←substitution_univ]
      apply ihBBU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_univ_sigma_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a a' A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = a →
                eqM ▸ A' = a' →
                  eqM ▸ 𝒰 = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n + 1 = m) (s : Tm (l + 1))
              (S : Tm l) (a a' A_1 : Tm m),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = a →
                  eqM ▸ B' = a' →
                    eqM ▸ 𝒰 = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a a' A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ ΣA;B) = a →
                  (eqM ▸ ΣA';B') = a' →
                    eqM ▸ 𝒰 = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A A' B B' hAAU hBBU ihAAU ihBBU m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.univ_sigma_eq
    · rw [←substitution_univ]
      apply ihAAU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [lift_n_substitution_shift]
      rw [extend_expand_context_n_substitution_shift]
      rw [←substitution_univ]
      apply ihBBU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_univ_nat_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) → Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ctx) →
      ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
        (a a' A : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝒩 = a →
            eqM ▸ 𝒩 = a' →
              eqM ▸ 𝒰 = A →
                (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                  Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.univ_nat_eq
    cases n with
    | zero =>
      have h := gen_ctx_neq Δ
      omega
    | succ n' =>
      cases Δ
      case start =>
        simp [substitute_shift_into_gen_ctx]
        simp [expand_ctx]
        simp [expand_ctx] at hiC
        apply hiC
      case expand Δ' T =>
        cases n' with
        | zero =>
          have h := gen_ctx_leq Δ'
          omega
        | succ m' =>
          apply ihiC
          · rfl
          · apply hsS
          · rfl

theorem weak_substitution_univ_iden_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (Γ ⊢ a₁ ≡ a₂ ∶ A) →
        (Γ ⊢ a₃ ≡ a₄ ∶ A) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a a' A_1 : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = a →
                  eqM ▸ A' = a' →
                    eqM ▸ 𝒰 = A_1 →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
            (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                (S : Tm l) (a a' A_1 : Tm m),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a₁ = a →
                    eqM ▸ a₂ = a' →
                      eqM ▸ A = A_1 →
                        (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                          Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a a' A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ a₃ = a →
                      eqM ▸ a₄ = a' →
                        eqM ▸ A = A_1 →
                          (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
                ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1))
                  (S : Tm l) (a a' A_1 : Tm m),
                  eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                    (eqM ▸ a₁ ≃[A] a₃) = a →
                      (eqM ▸ a₂ ≃[A'] a₄) = a' →
                        eqM ▸ 𝒰 = A_1 →
                          (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                            Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' ihAAU ihaaA ihaaA' m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.univ_iden_eq
    · rw [←substitution_univ]
      apply ihAAU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaaA'
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_ty_conv_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
    (Γ ⊢ a ≡ b ∶ A) →
      Γ ⊢ A ≡ B type →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a_3 a' A_1 : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ a = a_3 →
                eqM ▸ b = a' →
                  eqM ▸ A = A_1 →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_3⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (A_1 A' : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ B = A' →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ A_1⌈s↑/ₙleq⌉ ≡ A'⌈s↑/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_5 a' A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_5 →
                  eqM ▸ b = a' →
                    eqM ▸ B = A →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_5⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' a b A B habA hAB ihabA ihAB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    apply IsEqualTerm.ty_conv_eq
    · apply ihabA
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihAB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem weak_substitution_term_symm :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A : Tm n},
    (Γ ⊢ a ≡ a' ∶ A) →
      (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a_1 a'_1 A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ a = a_1 →
              eqM ▸ a' = a'_1 →
                eqM ▸ A = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_1⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉) →
        ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
          (a_2 a'_1 A_1 : Tm m),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ a' = a_2 →
              eqM ▸ a = a'_1 →
                eqM ▸ A = A_1 →
                  (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                    Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_2⌈s↑/ₙleq⌉ ≡ a'_1⌈s↑/ₙleq⌉ ∶ A_1⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' a a' A haaA ihaaA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.term_symm
    apply ihaaA
    · rfl
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem weak_substitution_term_trans :
    ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
    (Γ ⊢ a ≡ b ∶ T) →
      (Γ ⊢ b ≡ c ∶ T) →
        (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
            (a_1 a' A : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ a = a_1 →
                eqM ▸ b = a' →
                  eqM ▸ T = A →
                    (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                      Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_1⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a a' A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ b = a →
                  eqM ▸ c = a' →
                    eqM ▸ T = A →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l + 1 ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (s : Tm (l + 1)) (S : Tm l)
              (a_3 a' A : Tm m),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ a = a_3 →
                  eqM ▸ c = a' →
                    eqM ▸ T = A →
                      (Γ_1 ⬝ S ⊢ s ∶ S⌊↑ₚidₚ⌋) →
                        Γ_1 ⬝ S ⊗ ⌈s↑⌉(Δ w/Nat.le_refl (l + 1)) ⊢ a_3⌈s↑/ₙleq⌉ ≡ a'⌈s↑/ₙleq⌉ ∶ A⌈s↑/ₙleq⌉ :=
  by
    intro n Γ' S a b c habT hbcT ihabT ihbcT m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    apply IsEqualTerm.term_trans
    · apply ihabT
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihbcT
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

