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
import IMLTT.typed.proofs.admissable.WeakeningGeneral
import IMLTT.typed.proofs.admissable.DefeqReflTest

import IMLTT.typed.proofs.admissable.substitution.Helpers

theorem substitution_gen_var_eq : ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
   Γ ⊢ A type →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) {s S : Tm l}
         (A_1 : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x + 1 = m + 1) (s S : Tm l)
         (a a' A_1 : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
           eqM ▸ v(0) = a →
             eqM ▸ v(0) = a' →
               eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A hA ihA m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    cases n with
    | zero =>
      simp [substitute]
      simp [n_substitution]
      simp [substitute_var]
      rw [substitution_conv_zero]
      rw [substitution_shift_substitute_zero]
      cases Δ with
      | start =>
        cases heqΓ
        simp [substitute_into_gen_ctx]
        simp [expand_ctx]
        apply defeq_refl_term hsS
      | expand Δ' T =>
        have h1 := gen_ctx_leq Δ'
        omega
    | succ n' =>
      simp [substitute]
      simp [n_substitution]
      split
      case isTrue hT =>
        simp [substitute_var]
        simp [substitution_shift_id_lift]
        cases Δ with
        | start =>
          omega
        | expand Δ' T =>
          rw [←extend_expand_context] at heqΓ
          cases heqΓ
          apply IsEqualTerm.var_eq
          apply ihA
          · rfl
          · rfl
          · apply hsS
          · rfl
      case isFalse hF =>
        simp [substitute_var]
        rw [substitution_conv_zero]
        rw [substitution_shift_substitute_zero]
        split
        case h_1 =>
          cases Δ with
          | start =>
            cases heqΓ
            apply defeq_refl_term hsS
          | expand Δ' T =>
            have h1 := gen_ctx_leq Δ'
            omega
        case h_2 h =>
          cases Δ with
          | start =>
            cases heqΓ
            simp [expand_ctx]
            simp [weakening_id]
            cases h
          | expand Δ' T =>
            have h1 := gen_ctx_leq Δ'
            omega


theorem substitution_gen_weak_eq : ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
   (Γ ⊢ v(i) ≡ v(i) ∶ A) →
     Γ ⊢ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) (s S : Tm l)
           (a a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ v(i) = a →
               eqM ▸ v(i) = a' →
                 eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) {s S : Tm l}
             (A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A⌈s/ₙleq⌉ type) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x + 1 = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ v(i)⌊↑ₚidₚ⌋ = a →
                 eqM ▸ v(i)⌊↑ₚidₚ⌋ = a' →
                   eqM ▸ A⌊↑ₚidₚ⌋ = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n x Γ' A B hvvA hB ihvvA ihB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqt
    cases heqt'
    cases heqT
    simp_all
    cases n
    case zero =>
      simp [n_substitution]
      simp [substitution_conv_zero]
      simp [substitution_shift_substitute_zero]
      cases Δ with
      | start =>
        simp [expand_ctx]
        cases heqΓ
        apply hvvA
      | expand Δ' T =>
        have h := gen_ctx_neq Δ'
        omega
    case succ n' =>
      simp [n_substitution]
      split
      case isTrue hT =>
        simp [substitution_shift_id_lift]
        cases Δ with
        | start =>
          omega
        | expand Δ' T =>
          cases heqΓ
          have h := gen_ctx_leq Δ'
          simp_all
          simp [substitute_into_gen_ctx]
          simp [expand_ctx]
          apply weakening_term_eq
          · apply ihvvA
            · rfl
            · rfl
            · rfl
            · rfl
            · apply hsS
            · rfl
          · apply ihB
            · rfl
            · apply hsS
            · rfl
      case isFalse hF =>
        simp [substitution_conv_zero]
        simp [substitution_shift_substitute_zero]
        cases Δ with
        | start =>
          cases heqΓ
          apply hvvA
        | expand Δ' T =>
          have h := gen_ctx_leq Δ'
          omega

theorem substitution_gen_unit_comp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
   Γ ⬝ 𝟙 ⊢ A type →
     (Γ ⊢ a ∶ A⌈⋆⌉₀) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
           (A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ A⌈⋆⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A.indUnit ⋆ a = a_5 →
                 eqM ▸ a = a' →
                   eqM ▸ A⌈⋆⌉₀ = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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
      simp [lift_n_substitution]
      rw [←substitution_unit]
      rw [extend_expand_context_n_substitution]
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

theorem substitution_gen_pi_comp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
   (Γ ⬝ A ⊢ b ∶ B) →
     (Γ ⊢ a ∶ A) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
           (a A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ b = a → eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ (λA; b)◃a = a_5 →
                 eqM ▸ b⌈a⌉₀ = a' →
                   eqM ▸ B⌈a⌉₀ = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
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

theorem substitution_gen_sigma_comp : ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
   (Γ ⊢ a ∶ A) →
     (Γ ⊢ b ∶ B⌈a⌉₀) →
       (Γ ⬝ ΣA;B) ⊢ C type →
         (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
               (a_5 A_1 : Tm (m + 1 - 1 + 1)),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a = a_5 →
                   eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a_6 A : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ b = a_6 →
                     eqM ▸ B⌈a⌉₀ = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_6⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
                   (A_1 : Tm (m + 1 - 1 + 1)),
                   (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ C = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
                 (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                     (s S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                     eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ c = a →
                         eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 →
                           (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                   ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                     (a_9 a' A_1 : Tm (m + 1 - 1 + 1)),
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ A.indSigma B C c (a&b) = a_9 →
                         eqM ▸ c⌈(ₛidₚ), a, b⌉ = a' →
                           eqM ▸ C⌈a&b⌉₀ = A_1 →
                             (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_9⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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
      simp [←substitution_zero_lift]
      apply ihbB
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihC
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [subst_subst_sigma_C]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihcC
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_iden_comp : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a : Tm n},
   (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
     (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
       (Γ ⊢ a ∶ A) →
         Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 + 1 = m + 1)
               {s S : Tm l} (A_1 : Tm (m + 1 - 1 + 1)),
               (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a_6 A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ b = a_6 →
                     eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 →
                       (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_6⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                   (a_7 A_1 : Tm (m + 1 - 1 + 1)),
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ a = a_7 →
                       eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_7⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                 (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
                     (A_1 : Tm (m + 1 - 1 + 1)),
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 →
                         (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
                   ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                     (a_9 a' A_1 : Tm (m + 1 - 1 + 1)),
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ A.j B b a a (A.refl a) = a_9 →
                         eqM ▸ b = a' →
                           eqM ▸ B⌈(ₛidₚ), a, a, A.refl a⌉ = A_1 →
                             (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_9⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B b a hB hbB haA hB' ihB ihbB ihaA ihB' m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitute]
    rw [subst_subst_iden_elim]
    apply IsEqualTerm.iden_comp
    · simp [lift_subst_n]
      simp [lift_n_substitution]
      simp [←substitution_shift_id_lift]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      simp_all
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_subst_iden_propagate_subst]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihB
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_refl]
      rw [←subst_subst_iden_elim]
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
    · rw [←substitution_refl]
      rw [←subst_subst_iden_elim]
      apply ihB'
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_unit_intro_eq : ∀ {n : Nat} {Γ : Ctx n},
   Γ ctx →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
         (a a' A : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
           eqM ▸ ⋆ = a →
             eqM ▸ ⋆ = a' →
               eqM ▸ 𝟙 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_tt]
    simp [substitution_unit]
    apply IsEqualTerm.unit_intro_eq
    simp_all
    cases Δ
    case start =>
      simp [substitute_into_gen_ctx]
      simp [expand_ctx]
      simp [expand_ctx] at hiC
      exact ctx_decr hiC
    case expand Δ' T =>
      cases m with
      | zero =>
        have h := gen_ctx_leq Δ'
        omega
      | succ m' =>
        apply ihiC
        · exact hleq
        · rfl
        · apply hsS
        · rfl

theorem substitution_gen_unit_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
   Γ ⬝ 𝟙 ⊢ A ≡ A' type →
     (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀) →
       (Γ ⊢ b ≡ b' ∶ 𝟙) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
             (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = A_1 →
                 eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
               (a_5 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a = a_5 →
                   eqM ▸ a' = a'_1 →
                     eqM ▸ A⌈⋆⌉₀ = A_1 →
                       (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a a' A : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ b = a →
                     eqM ▸ b' = a' →
                       eqM ▸ 𝟙 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a_7 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A.indUnit b a = a_7 →
                     eqM ▸ A'.indUnit b' a' = a'_1 →
                       eqM ▸ A⌈b⌉₀ = A_1 →
                         (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_7⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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
      simp [lift_n_substitution]
      rw [←substitution_unit]
      rw [extend_expand_context_n_substitution]
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

theorem substitution_gen_empty_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
  Γ ⬝ 𝟘 ⊢ A ≡ A' type →
    (Γ ⊢ b ≡ b' ∶ 𝟘) →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
          (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
          eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ A = A_1 →
              eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a a' A : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ b = a →
                eqM ▸ b' = a' →
                  eqM ▸ 𝟘 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a a' A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A.indEmpty b = a →
                eqM ▸ A'.indEmpty b' = a' →
                  eqM ▸ A⌈b⌉₀ = A_1 →
                    (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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
      simp [lift_n_substitution]
      rw [←substitution_empty]
      rw [extend_expand_context_n_substitution]
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

theorem substitution_gen_pi_intro_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B) →
      Γ ⊢ A ≡ A' type →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
            (a a' A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ b = a →
                eqM ▸ b' = a' →
                  eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
              (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 →
                  eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
              (a a' A_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ λA; b) = a →
                  (eqM ▸ λA'; b') = a' →
                    (eqM ▸ ΠA;B) = A_1 →
                      (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
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

theorem substitution_gen_pi_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
   (Γ ⊢ f ≡ f' ∶ ΠA;B) →
     (Γ ⊢ a ≡ a' ∶ A) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ f = a →
               eqM ▸ f' = a' →
                 (eqM ▸ ΠA;B) = A_1 →
                   (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ a' = a'_1 →
                   eqM ▸ A = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a'_1 A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ f◃a = a_5 →
                 eqM ▸ f'◃a' = a'_1 →
                   eqM ▸ B⌈a⌉₀ = A →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
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

theorem substitution_gen_sigma_intro_eq : ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
   (Γ ⊢ a ≡ a' ∶ A) →
     (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a_3 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ a = a_3 →
               eqM ▸ a' = a'_1 →
                 eqM ▸ A = A_1 →
                   (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_3⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 a' A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ b = a_4 →
                 eqM ▸ b' = a' →
                   eqM ▸ B⌈a⌉₀ = A →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a&b = a_5 →
                 eqM ▸ a'&b' = a'_1 →
                   (eqM ▸ ΣA;B) = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' a a' A b b' B haaA hbbB ihaaA ihbbB m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
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

theorem substitution_gen_sigma_elim_eq : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)}
   {c c' : Tm (n + 1 + 1)},
   Γ ⊢ ΣA;B ≡ ΣA';B' type →
     (Γ ⊢ p ≡ p' ∶ ΣA;B) →
       (Γ ⬝ ΣA;B) ⊢ C ≡ C' type →
         (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
               (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 (eqM ▸ ΣA;B) = A_1 →
                   (eqM ▸ ΣA';B') = A'_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a a' A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ p = a →
                     eqM ▸ p' = a' →
                       (eqM ▸ ΣA;B) = A_1 →
                         (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
                   (A_1 A' : Tm (m + 1 - 1 + 1)),
                   (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ C = A_1 →
                       eqM ▸ C' = A' → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) →
                 (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                     (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                     eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ c = a →
                         eqM ▸ c' = a' →
                           eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ = A_1 →
                             (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                   ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                     (a a' A_1 : Tm (m + 1 - 1 + 1)),
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       eqM ▸ A.indSigma B C c p = a →
                         eqM ▸ A'.indSigma B' C' c' p' = a' →
                           eqM ▸ C⌈p⌉₀ = A_1 →
                             (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B A' B' p p' C C' c c' hSiSi hppSi hCC hccC ihSiSi ihppSi ihCC ihccC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_zero_lift]
    apply IsEqualTerm.sigma_elim_eq
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      rw [←substitution_sigma]
      apply ihSiSi
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
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihCC
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · simp [lift_subst_n]
      rw [subst_subst_sigma_C]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihccC
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_iden_intro_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
   Γ ⊢ A ≡ A' type →
     (Γ ⊢ a ≡ a' ∶ A) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ A = A_1 →
               eqM ▸ A' = A'_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ a' = a'_1 →
                   eqM ▸ A = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A.refl a = a_5 →
                 eqM ▸ A'.refl a' = a'_1 →
                   (eqM ▸ a ≃[A] a) = A_1 →
                     (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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

theorem substitution_gen_iden_elim_eq :
 ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' a₁ a₃ A' a₂ a₄ p p' : Tm n},
   (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type →
     (Γ ⊢ b ≡ b' ∶ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉) →
       Γ ⊢ a₁ ≃[A] a₃ ≡ a₂ ≃[A'] a₄ type →
         (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃) →
           Γ ⊢ B⌈(ₛidₚ), a₁, a₃, p⌉ type →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 + 1 = m + 1)
                 (s S : Tm l) (A_1 A' : Tm (m + 1 - 1 + 1)),
                 (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ B = A_1 →
                     eqM ▸ B' = A' → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) →
               (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                   (a a' A_1 : Tm (m + 1 - 1 + 1)),
                   eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                     eqM ▸ b = a →
                       eqM ▸ b' = a' →
                         eqM ▸ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉ = A_1 →
                           (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                 (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                     (A_1 A'_1 : Tm (m + 1 - 1 + 1)),
                     eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                       (eqM ▸ a₁ ≃[A] a₃) = A_1 →
                         (eqM ▸ a₂ ≃[A'] a₄) = A'_1 →
                           (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'_1⌈s/ₙleq⌉ type) →
                   (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                       (a a' A_1 : Tm (m + 1 - 1 + 1)),
                       eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                         eqM ▸ p = a →
                           eqM ▸ p' = a' →
                             (eqM ▸ a₁ ≃[A] a₃) = A_1 →
                               (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                         {s S : Tm l} (A : Tm (m + 1 - 1 + 1)),
                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                           eqM ▸ B⌈(ₛidₚ), a₁, a₃, p⌉ = A →
                             (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A⌈s/ₙleq⌉ type) →
                       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                         (s S : Tm l) (a a' A_1 : Tm (m + 1 - 1 + 1)),
                         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                           eqM ▸ A.j B b a₁ a₃ p = a →
                             eqM ▸ A'.j B' b' a₂ a₄ p' = a' →
                               eqM ▸ B⌈(ₛidₚ), a₁, a₃, p⌉ = A_1 →
                                 (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hIdId hppId hB' ihBB ihbbB ihIdId ihppId ihB'
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
      simp [lift_n_substitution]
      simp [←substitution_shift_id_lift]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      simp_all
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_subst_iden_propagate_subst]
      simp [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihBB
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_refl]
      rw [←subst_subst_iden_elim]
      apply ihbbB
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_iden]
      rw [←substitution_iden]
      apply ihIdId
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
    · rw [←subst_subst_iden_elim]
      apply ihB'
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_univ_unit_eq : ∀ {n : Nat} {Γ : Ctx n},
   Γ ctx →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
         (a a' A : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
           eqM ▸ 𝟙 = a →
             eqM ▸ 𝟙 = a' →
               eqM ▸ 𝒰 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_univ]
    simp [substitution_unit]
    apply IsEqualTerm.univ_unit_eq
    apply ihiC
    · apply hleq
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_univ_empty_eq : ∀ {n : Nat} {Γ : Ctx n},
   Γ ctx →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
       ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
         (a a' A : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
           eqM ▸ 𝟘 = a →
             eqM ▸ 𝟘 = a' →
               eqM ▸ 𝒰 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t t' T heqΓ heqt heqt' heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqt'
    cases heqT
    simp [substitution_univ]
    simp [substitution_empty]
    apply IsEqualTerm.univ_empty_eq
    apply ihiC
    · apply hleq
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_univ_pi_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
   (Γ ⊢ A ≡ A' ∶ 𝒰) →
     (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ A = a →
               eqM ▸ A' = a' →
                 eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ B = a →
                 eqM ▸ B' = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               (eqM ▸ ΠA;B) = a →
                 (eqM ▸ ΠA';B') = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [←substitution_univ]
      apply ihBBU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_univ_sigma_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
   (Γ ⊢ A ≡ A' ∶ 𝒰) →
     (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ A = a →
               eqM ▸ A' = a' →
                 eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ B = a →
                 eqM ▸ B' = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               (eqM ▸ ΣA;B) = a →
                 (eqM ▸ ΣA';B') = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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
      rw [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [←substitution_univ]
      apply ihBBU
      · rfl
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_univ_iden_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
   (Γ ⊢ A ≡ A' ∶ 𝒰) →
     (Γ ⊢ a₁ ≡ a₂ ∶ A) →
       (Γ ⊢ a₃ ≡ a₄ ∶ A) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a a' A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = a →
                 eqM ▸ A' = a' →
                   eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
               (a a' A_1 : Tm (m + 1 - 1 + 1)),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a₁ = a →
                   eqM ▸ a₂ = a' →
                     eqM ▸ A = A_1 →
                       (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a a' A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ a₃ = a →
                     eqM ▸ a₄ = a' →
                       eqM ▸ A = A_1 →
                         (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a a' A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   (eqM ▸ a₁ ≃[A] a₃) = a →
                     (eqM ▸ a₂ ≃[A'] a₄) = a' →
                       eqM ▸ 𝒰 = A_1 →
                         (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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

theorem substitution_gen_ty_conv_eq : ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
   (Γ ⊢ a ≡ b ∶ A) →
     Γ ⊢ A ≡ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a_3 a' A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ a = a_3 →
               eqM ▸ b = a' →
                 eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_3⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (A_1 A' : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = A_1 →
                 eqM ▸ B = A' → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 a' A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_5 →
                 eqM ▸ b = a' →
                   eqM ▸ B = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
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

theorem substitution_gen_term_symm : ∀ {n : Nat} {Γ : Ctx n} {a a' A : Tm n},
  (Γ ⊢ a ≡ a' ∶ A) →
  (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
      (a_1 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
        eqM ▸ a = a_1 →
          eqM ▸ a' = a'_1 →
            eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_1⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
    ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
      (a_2 a'_1 A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
        eqM ▸ a' = a_2 →
          eqM ▸ a = a'_1 →
            eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_2⌈s/ₙleq⌉ ≡ a'_1⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
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

theorem substitution_gen_term_trans : ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
 (Γ ⊢ a ≡ b ∶ T) →
   (Γ ⊢ b ≡ c ∶ T) →
     (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
         (a_1 a' A : Tm (m + 1 - 1 + 1)),
         eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
           eqM ▸ a = a_1 →
             eqM ▸ b = a' →
               eqM ▸ T = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_1⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a a' A : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ b = a →
               eqM ▸ c = a' →
                 eqM ▸ T = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
         ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a_3 a' A : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ a = a_3 →
               eqM ▸ c = a' →
                 eqM ▸ T = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_3⌈s/ₙleq⌉ ≡ a'⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
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
