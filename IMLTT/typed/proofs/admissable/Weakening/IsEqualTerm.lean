import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.admissable.weakening.Helpers
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem weakening_var_eq :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type →
      (∀ (l : Nat) {leq : l ≤ x} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from x l⌋ type) →
        ∀ (l : Nat) {leq : l ≤ x + 1} {B : Tm l},
          get_sub_context (Γ ⬝ A) l leq ⊢ B type →
            insert_into_ctx leq (Γ ⬝ A) B ⊢ v(0)⌊weaken_from (x + 1) l⌋ ≡ v(0)⌊weaken_from (x + 1) l⌋ ∶
              A⌊↑ₚidₚ⌋⌊weaken_from (x + 1) l⌋ :=
  by
    intro n Γ A hA ihA l hleq S hS
    cases hleq
    case refl =>
      simp [weaken_from]
      simp [weakening_comp]
      simp [comp_weaken]
      simp [insert_into_ctx]
      rw [←weakening_shift_id]
      rw (config := {occs := .pos [3]}) [←weakening_shift_id]
      simp [weakening_id]
      apply IsEqualTerm.weak_eq
      · apply IsEqualTerm.var_eq hA
      · rw [head_get_sub_context] at hS
        · apply hS
        · rfl
    case step h =>
      rw [←extend_insert_into_context (leq := h)]
      · simp [weakening_comp]
        simp [weaken_from]
        split
        case isTrue hT =>
          simp [comp_weaken]
          rw [←weakening_shift_id]
          simp [←weakening_comp]
          simp [weakening_id]
          simp [weaken]
          simp [weaken_var]
          apply IsEqualTerm.var_eq
          apply ihA
          rw [extend_get_sub_context] at hS
          apply hS
        case isFalse hF =>
          apply False.elim
          simp [h] at hF
          apply helper_weak_1 h hF

theorem weakening_weak_eq :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ≡ v(i) ∶ A) →
      Γ ⊢ B type →
        (∀ (l : Nat) {leq : l ≤ x} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type →
              insert_into_ctx leq Γ B ⊢ v(i)⌊weaken_from x l⌋ ≡ v(i)⌊weaken_from x l⌋ ∶ A⌊weaken_from x l⌋) →
          (∀ (l : Nat) {leq : l ≤ x} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type → insert_into_ctx leq Γ B_1 ⊢ B⌊weaken_from x l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ x + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ B) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ B) B_1 ⊢ v(i)⌊↑ₚidₚ⌋⌊weaken_from (x + 1) l⌋ ≡
                  v(i)⌊↑ₚidₚ⌋⌊weaken_from (x + 1) l⌋ ∶ A⌊↑ₚidₚ⌋⌊weaken_from (x + 1) l⌋ :=
  by
    intro n x Γ A B hvA hB ihvA ihB l hleq S hS
    · cases hleq
      case refl =>
        simp [insert_into_ctx]
        simp [weaken_from]
        apply IsEqualTerm.weak_eq
        · rw [←weakening_conv_var]
          rw [head_get_sub_context (eq := by rfl)] at hS
          rw [head_insert_into_context]
          · cases n with
            | zero =>
              simp [weaken_from]
              rw [←head_insert_into_context]
              apply IsEqualTerm.weak_eq
              · apply hvA
              · apply hB
            | succ n' =>
              rw [←head_insert_into_context]
              apply IsEqualTerm.weak_eq
              · apply hvA
              · apply hB
        · rw [head_get_sub_context] at hS
          · apply hS
          · rfl
      case step h =>
        rw [shift_weaken_from]
        · rw [shift_weaken_from]
          · rw [←extend_insert_into_context]
            apply IsEqualTerm.weak_eq
            · simp [←weakening_conv_var]
              apply ihvA
              rw [extend_get_sub_context] at hS
              apply hS
            · apply ihB
              rw [extend_get_sub_context] at hS
              apply hS
            · apply h
          · exact h
        · exact h

theorem weakening_unit_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
    Γ ⬝ 𝟙 ⊢ A type →
      (Γ ⊢ a ∶ A⌈⋆⌉₀) →
        (∀ (l : Nat) {leq : l ≤ n + 1} {B : Tm l},
            get_sub_context (Γ ⬝ 𝟙) l leq ⊢ B type → insert_into_ctx leq (Γ ⬝ 𝟙) B ⊢ A⌊weaken_from (n + 1) l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌈⋆⌉₀⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ A.indUnit ⋆ a⌊weaken_from n l⌋ ≡ a⌊weaken_from n l⌋ ∶ A⌈⋆⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ A a hA haA ihA ihaA l hleq S hS
    rw [weak_sub_zero]
    apply IsEqualTerm.unit_comp
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [←weakening_unit]
      rw [extend_insert_into_context]
      · apply ihA
        rw [extend_get_sub_context]
        apply hS
      · exact hleq
    · simp [lift_weak_n]
      simp [lift_single_subst_tt]
      apply ihaA
      apply hS

theorem weakening_pi_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
    (Γ ⬝ A ⊢ b ∶ B) →
      (Γ ⊢ a ∶ A) →
        (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
            get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
              insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ b⌊weaken_from (n + 1) l⌋ ∶ B⌊weaken_from (n + 1) l⌋) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ (λA; b)◃a⌊weaken_from n l⌋ ≡ b⌈a⌉₀⌊weaken_from n l⌋ ∶ B⌈a⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ A b B a hbB haA ihbB ihaA l hleq S hS
    rw [weak_sub_zero]
    rw [weak_sub_zero]
    apply IsEqualTerm.pi_comp
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [extend_insert_into_context]
      · apply ihbB
        rw [extend_get_sub_context]
        apply hS
      · exact hleq
    · apply ihaA
      apply hS

theorem weakening_sigma_comp :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
    (Γ ⊢ a ∶ A) →
      (Γ ⊢ b ∶ B⌈a⌉₀) →
        (Γ ⬝ ΣA;B) ⊢ C type →
          (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                  get_sub_context Γ l leq ⊢ B_1 type →
                    insert_into_ctx leq Γ B_1 ⊢ b⌊weaken_from n l⌋ ∶ B⌈a⌉₀⌊weaken_from n l⌋) →
                (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
                    get_sub_context (Γ ⬝ ΣA;B) l leq ⊢ B_1 type →
                      insert_into_ctx leq (Γ ⬝ ΣA;B) B_1 ⊢ C⌊weaken_from (n + 1) l⌋ type) →
                  (∀ (l : Nat) {leq : l ≤ n + 1 + 1} {B_1 : Tm l},
                      get_sub_context (Γ ⬝ A ⬝ B) l leq ⊢ B_1 type →
                        insert_into_ctx leq (Γ ⬝ A ⬝ B) B_1 ⊢ c⌊weaken_from (n + 1 + 1) l⌋ ∶
                          C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉⌊weaken_from (n + 1 + 1) l⌋) →
                    ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                      get_sub_context Γ l leq ⊢ B_1 type →
                        insert_into_ctx leq Γ B_1 ⊢ A.indSigma B C c (a&b)⌊weaken_from n l⌋ ≡
                          c⌈(ₛidₚ), a, b⌉⌊weaken_from n l⌋ ∶ C⌈a&b⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ a A b B C c haA hbB hC hcC ihaA ihbB ihC ihcC l hleq S hS
    rw [weak_sub_zero]
    rw [weak_subst_sigma_c]
    apply IsEqualTerm.sigma_comp
    · apply ihaA
      apply hS
    · simp [lift_weak_n]
      rw [←weak_sub_zero]
      apply ihbB
      apply hS
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      · rw (config := {occs := .pos [1]}) [←lift_weaken_from]
        · rw [←weakening_sigma]
          rw [extend_insert_into_context]
          apply ihC
          rw [extend_get_sub_context]
          apply hS
        · exact hleq
      · exact hleq
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      · rw [lift_weaken_from]
        · rw [weak_subst_sigma_C]
          · simp [extend_insert_into_context]
            apply ihcC
            rw [extend_get_sub_context]
            · rw [extend_get_sub_context]
              apply hS
          · exact hleq
        · omega
      · omega

theorem weakening_iden_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
      (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
        (Γ ⊢ a ∶ A) →
          Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
            (∀ (l : Nat) {leq : l ≤ n + 1 + 1 + 1} {B_1 : Tm l},
                get_sub_context (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) l leq ⊢ B_1 type →
                  insert_into_ctx leq (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) B_1 ⊢
                    B⌊weaken_from (n + 1 + 1 + 1) l⌋ type) →
              (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                  get_sub_context Γ l leq ⊢ B_1 type →
                    insert_into_ctx leq Γ B_1 ⊢ b⌊weaken_from n l⌋ ∶ B⌈(ₛidₚ), a, a, A.refl a⌉⌊weaken_from n l⌋) →
                (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                    get_sub_context Γ l leq ⊢ B type →
                      insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
                  (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                      get_sub_context Γ l leq ⊢ B_1 type →
                        insert_into_ctx leq Γ B_1 ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉⌊weaken_from n l⌋ type) →
                    ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                      get_sub_context Γ l leq ⊢ B_1 type →
                        insert_into_ctx leq Γ B_1 ⊢ A.j B b a a (A.refl a)⌊weaken_from n l⌋ ≡ b⌊weaken_from n l⌋ ∶
                          B⌈(ₛidₚ), a, a, A.refl a⌉⌊weaken_from n l⌋ :=
  by
    intro n Γ A B b a hB hbB haA hB' ihB ihbB ihaA ihB' l hleq s hS
    rw [weak_subst_iden_elim]
    apply IsEqualTerm.iden_comp
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [lift_weaken_from]
      rw [lift_weaken_from]
      rw [extend_insert_into_context]
      rw [←shift_weaken_from]
      rw [extend_insert_into_context]
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←shift_weaken_from]
      rw [←shift_weaken_from]
      rw [weakening_shift_id]
      rw [←helper_weak_iden_propagate_weak]
      rw [extend_insert_into_context]
      apply ihB
      rw [extend_get_sub_context]
      rw [extend_get_sub_context]
      rw [extend_get_sub_context]
      apply hS
      any_goals omega
    · rw [helper_weak_refl_propagate_weak]
      rw [←weak_subst_iden_elim]
      apply ihbB
      apply hS
    · apply ihaA
      apply hS
    · rw [helper_weak_refl_propagate_weak]
      rw [←weak_subst_iden_elim]
      apply ihB'
      apply hS

theorem weakening_unit_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type →
            insert_into_ctx leq Γ B ⊢ ⋆⌊weaken_from n l⌋ ≡ ⋆⌊weaken_from n l⌋ ∶ 𝟙⌊weaken_from n l⌋ :=
  by
    intro n Γ hiC ihiC l hleq S hS
    apply IsEqualTerm.unit_intro_eq
    apply ihiC
    apply hS

theorem weakening_unit_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
    Γ ⬝ 𝟙 ⊢ A ≡ A' type →
      (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀) →
        (Γ ⊢ b ≡ b' ∶ 𝟙) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B : Tm l},
              get_sub_context (Γ ⬝ 𝟙) l leq ⊢ B type →
                insert_into_ctx leq (Γ ⬝ 𝟙) B ⊢ A⌊weaken_from (n + 1) l⌋ ≡ A'⌊weaken_from (n + 1) l⌋ type) →
            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                get_sub_context Γ l leq ⊢ B type →
                  insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌈⋆⌉₀⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ b⌊weaken_from n l⌋ ≡ b'⌊weaken_from n l⌋ ∶ 𝟙⌊weaken_from n l⌋) →
                ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ A.indUnit b a⌊weaken_from n l⌋ ≡ A'.indUnit b' a'⌊weaken_from n l⌋ ∶
                      A⌈b⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihbb1 l hleq S hS
    rw [weak_sub_zero]
    apply IsEqualTerm.unit_elim_eq
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [←weakening_unit]
      rw [extend_insert_into_context]
      · apply ihAA
        rw [extend_get_sub_context]
        apply hS
      · exact hleq
    · simp [lift_weak_n]
      simp [lift_single_subst_tt]
      apply ihaaA
      apply hS
    · apply ihbb1
      apply hS

theorem weakening_empty_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
    Γ ⬝ 𝟘 ⊢ A ≡ A' type →
      (Γ ⊢ b ≡ b' ∶ 𝟘) →
        (∀ (l : Nat) {leq : l ≤ n + 1} {B : Tm l},
            get_sub_context (Γ ⬝ 𝟘) l leq ⊢ B type →
              insert_into_ctx leq (Γ ⬝ 𝟘) B ⊢ A⌊weaken_from (n + 1) l⌋ ≡ A'⌊weaken_from (n + 1) l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ b⌊weaken_from n l⌋ ≡ b'⌊weaken_from n l⌋ ∶ 𝟘⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ A.indEmpty b⌊weaken_from n l⌋ ≡ A'.indEmpty b'⌊weaken_from n l⌋ ∶
                  A⌈b⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ A A' b b' hAA hbb0 ihAA ihbb0 l hleq S hS
    rw [weak_sub_zero]
    apply IsEqualTerm.empty_elim_eq
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [←weakening_empty]
      rw [extend_insert_into_context]
      · apply ihAA
        rw [extend_get_sub_context]
        apply hS
      · exact hleq
    · apply ihbb0
      apply hS

theorem weakening_pi_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B) →
      Γ ⊢ A ≡ A' type →
        (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
            get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
              insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ b⌊weaken_from (n + 1) l⌋ ≡ b'⌊weaken_from (n + 1) l⌋ ∶
                B⌊weaken_from (n + 1) l⌋) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ (λA; b)⌊weaken_from n l⌋ ≡ (λA'; b')⌊weaken_from n l⌋ ∶
                  (ΠA;B)⌊weaken_from n l⌋ :=
  by
    intro n Γ A A' b b' B hbbB hPiPi ihbbB ihPiPi l hleq S hS
    apply IsEqualTerm.pi_intro_eq
    · rw [extend_insert_into_context]
      simp [lift_weak_n]
      rw [lift_weaken_from]
      · apply ihbbB
        simp [get_sub_context]
        split
        · exact hS
        · omega
      · omega
    · apply ihPiPi
      apply hS

theorem weakening_pi_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
    (Γ ⊢ f ≡ f' ∶ ΠA;B) →
      (Γ ⊢ a ≡ a' ∶ A) →
        (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
            get_sub_context Γ l leq ⊢ B_1 type →
              insert_into_ctx leq Γ B_1 ⊢ f⌊weaken_from n l⌋ ≡ f'⌊weaken_from n l⌋ ∶ (ΠA;B)⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ f◃a⌊weaken_from n l⌋ ≡ f'◃a'⌊weaken_from n l⌋ ∶ B⌈a⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ f f' A B a a' hffPi haaA ihffPi ihaaA l hleq s hS
    rw [weak_sub_zero]
    apply IsEqualTerm.pi_elim_eq
    · apply ihffPi
      apply hS
    · apply ihaaA
      apply hS

theorem weakening_sigma_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ≡ a' ∶ A) →
      (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀) →
        Γ ⬝ A ⊢ B type →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
            (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                get_sub_context Γ l leq ⊢ B_1 type →
                  insert_into_ctx leq Γ B_1 ⊢ b⌊weaken_from n l⌋ ≡ b'⌊weaken_from n l⌋ ∶ B⌈a⌉₀⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
                  get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                    insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ type) →
                ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                  get_sub_context Γ l leq ⊢ B_1 type →
                    insert_into_ctx leq Γ B_1 ⊢ a&b⌊weaken_from n l⌋ ≡ a'&b'⌊weaken_from n l⌋ ∶ (ΣA;B)⌊weaken_from n l⌋ :=
  by
    intro n Γ a a' A b b' B haaA hbbB hB ihaaA ihbbB ihB l hleq S hS
    apply IsEqualTerm.sigma_intro_eq
    · apply ihaaA
      apply hS
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      · simp [weaken_from]
        split
        case a.isTrue h =>
          rw [←weak_sub_zero]
          apply ihbbB
          apply hS
        case a.isFalse h =>
          omega
      · exact hleq
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [extend_insert_into_context]
      apply ihB
      rw [extend_get_sub_context]
      apply hS
      any_goals omega

theorem weakening_sigma_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)}
    {c c' : Tm (n + 1 + 1)},
    Γ ⊢ A ≡ A' type →
      Γ ⬝ A ⊢ B ≡ B' type →
        (Γ ⊢ p ≡ p' ∶ ΣA;B) →
          (Γ ⬝ ΣA;B) ⊢ C ≡ C' type →
            (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
              (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) →
                (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
                    get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                      insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ ≡ B'⌊weaken_from (n + 1) l⌋ type) →
                  (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                      get_sub_context Γ l leq ⊢ B_1 type →
                        insert_into_ctx leq Γ B_1 ⊢ p⌊weaken_from n l⌋ ≡ p'⌊weaken_from n l⌋ ∶ (ΣA;B)⌊weaken_from n l⌋) →
                    (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
                        get_sub_context (Γ ⬝ ΣA;B) l leq ⊢ B_1 type →
                          insert_into_ctx leq (Γ ⬝ ΣA;B) B_1 ⊢ C⌊weaken_from (n + 1) l⌋ ≡
                            C'⌊weaken_from (n + 1) l⌋ type) →
                      (∀ (l : Nat) {leq : l ≤ n + 1 + 1} {B_1 : Tm l},
                          get_sub_context (Γ ⬝ A ⬝ B) l leq ⊢ B_1 type →
                            insert_into_ctx leq (Γ ⬝ A ⬝ B) B_1 ⊢ c⌊weaken_from (n + 1 + 1) l⌋ ≡
                              c'⌊weaken_from (n + 1 + 1) l⌋ ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉⌊weaken_from (n + 1 + 1) l⌋) →
                        ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                          get_sub_context Γ l leq ⊢ B_1 type →
                            insert_into_ctx leq Γ B_1 ⊢ A.indSigma B C c p⌊weaken_from n l⌋ ≡
                              A'.indSigma B' C' c' p'⌊weaken_from n l⌋ ∶ C⌈p⌉₀⌊weaken_from n l⌋ :=
  by
    intro n Γ A B A' B' p p' C C' c c' hAA hBB hppSi hCC hccC ihAA ihBB ihppSi ihCC ihccC l hleq S hS
    rw [weak_sub_zero]
    apply IsEqualTerm.sigma_elim_eq
    · apply ihAA
      apply hS
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [extend_insert_into_context]
      apply ihBB
      rw [extend_get_sub_context]
      apply hS
      any_goals omega
    · apply ihppSi
      apply hS
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      · rw (config := {occs := .pos [1]}) [←lift_weaken_from]
        · rw [←weakening_sigma]
          rw [extend_insert_into_context]
          apply ihCC
          rw [extend_get_sub_context]
          apply hS
        · exact hleq
      · exact hleq
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      · rw [lift_weaken_from]
        · rw [weak_subst_sigma_C]
          · simp [extend_insert_into_context]
            apply ihccC
            rw [extend_get_sub_context]
            · rw [extend_get_sub_context]
              apply hS
          · exact hleq
        · omega
      · omega

theorem weakening_iden_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
    Γ ⊢ A ≡ A' type →
      (Γ ⊢ a ≡ a' ∶ A) →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ A.refl a⌊weaken_from n l⌋ ≡ A'.refl a'⌊weaken_from n l⌋ ∶
                  (a ≃[A] a)⌊weaken_from n l⌋ :=
  by
    intro n Γ A A' a a' hAA haaA ihAA ihaaA l hleq S hS
    apply IsEqualTerm.iden_intro_eq
    · apply ihAA
      apply hS
    · apply ihaaA
      apply hS

theorem weakening_iden_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' a₁ a₃ A' a₂ a₄ p p' : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type →
    (Γ ⊢ b ≡ b' ∶ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉) →
      Γ ⊢ A ≡ A' type →
        (Γ ⊢ a₁ ≡ a₂ ∶ A) →
          (Γ ⊢ a₃ ≡ a₄ ∶ A') →
            (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃) →
              Γ ⊢ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉ ≡ B'⌈(ₛidₚ), a₂, a₂, A'.refl a₂⌉ type →
                Γ ⊢ B⌈(ₛidₚ), a₁, a₃, p⌉ ≡ B'⌈(ₛidₚ), a₂, a₄, p'⌉ type →
                  (∀ (l : Nat) {leq : l ≤ n + 1 + 1 + 1} {B_1 : Tm l},
                      get_sub_context (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) l leq ⊢ B_1 type →
                        insert_into_ctx leq (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) B_1 ⊢
                          B⌊weaken_from (n + 1 + 1 + 1) l⌋ ≡ B'⌊weaken_from (n + 1 + 1 + 1) l⌋ type) →
                    (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                        get_sub_context Γ l leq ⊢ B_1 type →
                          insert_into_ctx leq Γ B_1 ⊢ b⌊weaken_from n l⌋ ≡ b'⌊weaken_from n l⌋ ∶
                            B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉⌊weaken_from n l⌋) →
                      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                          get_sub_context Γ l leq ⊢ B type →
                            insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ type) →
                        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                            get_sub_context Γ l leq ⊢ B type →
                              insert_into_ctx leq Γ B ⊢ a₁⌊weaken_from n l⌋ ≡ a₂⌊weaken_from n l⌋ ∶
                                A⌊weaken_from n l⌋) →
                          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                              get_sub_context Γ l leq ⊢ B type →
                                insert_into_ctx leq Γ B ⊢ a₃⌊weaken_from n l⌋ ≡ a₄⌊weaken_from n l⌋ ∶
                                  A'⌊weaken_from n l⌋) →
                            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                                get_sub_context Γ l leq ⊢ B type →
                                  insert_into_ctx leq Γ B ⊢ p⌊weaken_from n l⌋ ≡ p'⌊weaken_from n l⌋ ∶
                                    (a₁ ≃[A] a₃)⌊weaken_from n l⌋) →
                              (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                                  get_sub_context Γ l leq ⊢ B_1 type →
                                    insert_into_ctx leq Γ B_1 ⊢ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉⌊weaken_from n l⌋ ≡
                                      B'⌈(ₛidₚ), a₂, a₂, A'.refl a₂⌉⌊weaken_from n l⌋ type) →
                                (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                                    get_sub_context Γ l leq ⊢ B_1 type →
                                      insert_into_ctx leq Γ B_1 ⊢ B⌈(ₛidₚ), a₁, a₃, p⌉⌊weaken_from n l⌋ ≡
                                        B'⌈(ₛidₚ), a₂, a₄, p'⌉⌊weaken_from n l⌋ type) →
                                  ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
                                    get_sub_context Γ l leq ⊢ B_1 type →
                                      insert_into_ctx leq Γ B_1 ⊢ A.j B b a₁ a₃ p⌊weaken_from n l⌋ ≡
                                        A'.j B' b' a₂ a₄ p'⌊weaken_from n l⌋ ∶ B⌈(ₛidₚ), a₁, a₃, p⌉⌊weaken_from n l⌋ :=
  by
    intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p' 
    intro hBB hbbB hAA haaA haaA' hppId hBBa hBBc ihBB ihbbB ihAA ihaaA ihaaA' ihppId ihBBa ihBBc l hleq S hS
    rw [weak_subst_iden_elim]
    apply IsEqualTerm.iden_elim_eq
    · simp [lift_weak_n]
      rw [lift_weaken_from]
      rw [lift_weaken_from]
      rw [lift_weaken_from]
      rw [extend_insert_into_context]
      rw [←shift_weaken_from]
      rw [extend_insert_into_context]
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←shift_weaken_from]
      rw [←shift_weaken_from]
      rw [weakening_shift_id]
      rw [←helper_weak_iden_propagate_weak]
      rw [extend_insert_into_context]
      apply ihBB
      rw [extend_get_sub_context]
      rw [extend_get_sub_context]
      rw [extend_get_sub_context]
      apply hS
      any_goals omega
    · rw [helper_weak_refl_propagate_weak]
      rw [←weak_subst_iden_elim]
      apply ihbbB
      apply hS
    · apply ihAA
      apply hS
    · apply ihaaA
      apply hS
    · apply ihaaA'
      apply hS
    · apply ihppId
      apply hS
    · simp [←weakening_refl]
      rw [←weak_subst_iden_elim]
      rw [←weak_subst_iden_elim]
      apply ihBBa
      apply hS
    · rw [←weak_subst_iden_elim]
      rw [←weak_subst_iden_elim]
      apply ihBBc
      apply hS

theorem weakening_univ_unit_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type →
            insert_into_ctx leq Γ B ⊢ 𝟙⌊weaken_from n l⌋ ≡ 𝟙⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ hiC ihiC l hleq S hS
    simp [weaken]
    apply IsEqualTerm.univ_unit_eq
    apply ihiC
    apply hS

theorem weakening_univ_empty_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l}, get_sub_context Γ l leq ⊢ B type → insert_into_ctx leq Γ B ctx) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type →
            insert_into_ctx leq Γ B ⊢ 𝟘⌊weaken_from n l⌋ ≡ 𝟘⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ hiC ihiC l hleq S hS
    simp [weaken]
    apply IsEqualTerm.univ_empty_eq
    apply ihiC
    apply hS

theorem weakening_univ_pi_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type →
              insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ ≡ B'⌊weaken_from (n + 1) l⌋ ∶
                  𝒰⌊weaken_from (n + 1) l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ (ΠA;B)⌊weaken_from n l⌋ ≡ (ΠA';B')⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ A A' B B' hAAU hBBU ihAAU ihBBU l hleq S hS
    simp [weaken] at *
    simp [lift_weak_n]
    apply IsEqualTerm.univ_pi_eq
    · apply ihAAU
      · apply hS
    · rw [extend_insert_into_context]
      rw [lift_weaken_from]
      apply ihBBU
      simp [get_sub_context]
      split
      · exact hS
      · omega
      omega

theorem weakening_univ_sigma_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type →
              insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n + 1} {B_1 : Tm l},
              get_sub_context (Γ ⬝ A) l leq ⊢ B_1 type →
                insert_into_ctx leq (Γ ⬝ A) B_1 ⊢ B⌊weaken_from (n + 1) l⌋ ≡ B'⌊weaken_from (n + 1) l⌋ ∶
                  𝒰⌊weaken_from (n + 1) l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ (ΣA;B)⌊weaken_from n l⌋ ≡ (ΣA';B')⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ A A' B B' hAAU hBBU ihAAU ihBBU l hleq S hS
    simp [weaken] at *
    simp [lift_weak_n]
    apply IsEqualTerm.univ_sigma_eq
    · apply ihAAU
      · apply hS
    · rw [extend_insert_into_context]
      rw [lift_weaken_from]
      apply ihBBU
      simp [get_sub_context]
      split
      · exact hS
      · omega
      omega

theorem weakening_univ_iden_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (Γ ⊢ a₁ ≡ a₂ ∶ A) →
        (Γ ⊢ a₃ ≡ a₄ ∶ A) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ A⌊weaken_from n l⌋ ≡ A'⌊weaken_from n l⌋ ∶ 𝒰⌊weaken_from n l⌋) →
            (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                get_sub_context Γ l leq ⊢ B type →
                  insert_into_ctx leq Γ B ⊢ a₁⌊weaken_from n l⌋ ≡ a₂⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
              (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ a₃⌊weaken_from n l⌋ ≡ a₄⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
                ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
                  get_sub_context Γ l leq ⊢ B type →
                    insert_into_ctx leq Γ B ⊢ (a₁ ≃[A] a₃)⌊weaken_from n l⌋ ≡ (a₂ ≃[A'] a₄)⌊weaken_from n l⌋ ∶
                      𝒰⌊weaken_from n l⌋ :=
  by
    intro n Γ A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' ihAAU ihaaA ihaaA' l hleq S hS
    simp [weaken]
    apply IsEqualTerm.univ_iden_eq
    · apply ihAAU
      · apply hS
    · apply ihaaA
      · apply hS
    · apply ihaaA'
      · apply hS

theorem weakening_ty_conv_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
    (Γ ⊢ a ≡ b ∶ A) →
      Γ ⊢ A ≡ B type →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type →
              insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ≡ b⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ A⌊weaken_from n l⌋ ≡ B⌊weaken_from n l⌋ type) →
            ∀ (l : Nat) {leq : l ≤ n} {B_1 : Tm l},
              get_sub_context Γ l leq ⊢ B_1 type →
                insert_into_ctx leq Γ B_1 ⊢ a⌊weaken_from n l⌋ ≡ b⌊weaken_from n l⌋ ∶ B⌊weaken_from n l⌋ :=
  by
    intro n Γ a b A B habA hAB ihabA ihAB l hleq S hS
    apply IsEqualTerm.ty_conv_eq
    · apply ihabA
      apply hS
    · apply ihAB
      apply hS

theorem weakening_term_symm :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A : Tm n},
    (Γ ⊢ a ≡ a' ∶ A) →
      (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type →
            insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ≡ a'⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋) →
        ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
          get_sub_context Γ l leq ⊢ B type →
            insert_into_ctx leq Γ B ⊢ a'⌊weaken_from n l⌋ ≡ a⌊weaken_from n l⌋ ∶ A⌊weaken_from n l⌋ :=
  by
    intro n Γ a a' A haaA ihaaA l hleq S hS
    apply IsEqualTerm.term_symm
    apply ihaaA
    apply hS

theorem weakening_term_trans :
    ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
    (Γ ⊢ a ≡ b ∶ T) →
      (Γ ⊢ b ≡ c ∶ T) →
        (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
            get_sub_context Γ l leq ⊢ B type →
              insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ≡ b⌊weaken_from n l⌋ ∶ T⌊weaken_from n l⌋) →
          (∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ b⌊weaken_from n l⌋ ≡ c⌊weaken_from n l⌋ ∶ T⌊weaken_from n l⌋) →
            ∀ (l : Nat) {leq : l ≤ n} {B : Tm l},
              get_sub_context Γ l leq ⊢ B type →
                insert_into_ctx leq Γ B ⊢ a⌊weaken_from n l⌋ ≡ c⌊weaken_from n l⌋ ∶ T⌊weaken_from n l⌋ :=
  by
    intro n Γ T a b C habT hbcT ihabT ihbcT l hleq S hS
    apply IsEqualTerm.term_trans
    · apply ihabT
      apply hS
    · apply ihbcT
      apply hS
