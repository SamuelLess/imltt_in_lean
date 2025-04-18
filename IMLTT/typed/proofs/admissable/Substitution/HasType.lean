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
import IMLTT.typed.proofs.admissable.Weakening

import IMLTT.typed.proofs.admissable.substitution.Helpers

theorem substitution_gen_var :
 ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) {s S : Tm l}
          (A_1 : Tm (m + 1 - 1 + 1)),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ type) →
        ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x + 1 = m + 1) (s S : Tm l)
          (a A_1 : Tm (m + 1 - 1 + 1)),
          eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ v(0) = a → eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A hA ihA m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqt
    cases heqT
    cases Δ with
    | start =>
      replace_by_conclusion hsS
      · substitution_step
      · apply hsS
    | expand Δ' S' =>
      cases heqΓ
      cases n with
      | zero =>
        cases hleq
        replace_by_conclusion hsS
        · apply congr
          · substitution_step
          · substitution_step
        · apply hsS
      | succ n' =>
        replace_by_conclusion HasType.var
        · apply congr
          · substitution_step
          · substitution_step
        · apply HasType.var
          apply ihA
          repeat' rfl
          apply hsS

theorem substitution_gen_weak : ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
  (Γ ⊢ v(i) ∶ A) →
    Γ ⊢ B type →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) (s S : Tm l)
          (a A_1 : Tm (m + 1 - 1 + 1)),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
            eqM ▸ v(i) = a → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) {s S : Tm l}
            (A : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ B = A → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A⌈s/ₙleq⌉ type) →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x + 1 = m + 1) (s S : Tm l)
            (a A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ v(i)⌊↑ₚidₚ⌋ = a →
                eqM ▸ A⌊↑ₚidₚ⌋ = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n x Γ' A B hvA hB ihvA ihB m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqt
    cases heqT
    cases n
    case zero =>
      simp [n_substitution]
      cases Δ with
      | start =>
        cases heqΓ
        replace_by_conclusion hvA
        · substitution_step
        · apply hvA
      | expand Δ' T =>
        have h := gen_ctx_neq Δ'
        omega
    case succ n' =>
      simp [n_substitution]
      split
      case isTrue hT =>
        cases Δ with
        | start =>
          omega
        | expand Δ' T =>
          cases heqΓ
          have h := gen_ctx_leq Δ'
          replace_by_conclusion weakening_term
          · apply congr
            apply congr
            · rfl
            · substitution_step
            · substitution_step
              rw [←substitution_conv_shift_id]
          · apply weakening_term
            · rw [←substitution_conv_var]
              apply ihvA
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
      case isFalse hF =>
        cases Δ with
        | start =>
          cases heqΓ
          replace_by_conclusion hvA
          · substitution_step
          · apply hvA
        | expand Δ' T =>
          have h := gen_ctx_leq Δ'
          omega

theorem substitution_gen_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ ⋆ = a → eqM ▸ 𝟙 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.unit_intro
    cases Δ
    case start =>
      exact ctx_decr hiC
    case expand Δ' T =>
      apply ihiC
      repeat' rfl
      apply hsS

theorem substitution_gen_pi_intro : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
  (Γ ⬝ A ⊢ b ∶ B) →
    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
        (a A_1 : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ b = a → eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A_1 : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          (eqM ▸ λA; b) = a →
            (eqM ▸ ΠA;B) = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A b B hbB ihbB m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.pi_intro
    replace_by_conclusion ihbB
    · apply congr
      apply congr
      apply congr
      · rfl
      · substitution_step
      · substitution_step
      · substitution_step
    · apply ihbB
      repeat' rfl
      apply hsS

theorem substitution_gen_sigma_intro : 
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
  (Γ ⊢ a ∶ A) →
    (Γ ⊢ b ∶ B⌈a⌉₀) →
      Γ ⬝ A ⊢ B type →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a_4 A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ a = a_4 →
                eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
              (a_5 A : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ b = a_5 →
                  eqM ▸ B⌈a⌉₀ = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
                (A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                (a_7 A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ a&b = a_7 →
                    (eqM ▸ ΣA;B) = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_7⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' a A b B haA hbB hB ihaA ihbB ihB m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.sigma_intro
    · apply ihaA
      repeat' rfl
      apply hsS
    · replace_by_conclusion ihbB
      · apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
        · substitution_step
        · simp only [lift_subst_n]
          rw [←substitution_zero_lift]
      · apply ihbB
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihB
      · apply congr
        apply congr
        · rfl
        · substitution_step
        · substitution_step
      · apply ihB
        repeat' rfl
        apply hsS

theorem substitution_gen_nat_zero_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝓏 = a → eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.nat_zero_intro
    cases Δ
    case start =>
      exact ctx_decr hiC
    case expand Δ' T =>
      apply ihiC
      repeat' rfl
      apply hsS

theorem substitution_gen_nat_succ_intro :
    ∀ {n : Nat} {Γ : Ctx n} {x : Tm n},
    (Γ ⊢ x ∶ 𝒩) →
    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ x = a → eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝓈(x) = a → eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' x hxNat ihxNat m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.nat_succ_intro
    rw [←substitution_nat]
    apply ihxNat
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_iden_intro :  ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
  Γ ⊢ A type →
    (Γ ⊢ a ∶ A) →
      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
          (A_1 : Tm (m + 1 - 1 + 1)),
          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a_4 A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ a = a_4 →
                eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
          ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a_5 A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A.refl a = a_5 →
                (eqM ▸ a ≃[A] a) = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A a hA haA ihA ihaA m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    apply HasType.iden_intro
    · apply ihA
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

theorem substitution_gen_univ_unit : ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝟙 = a → eqM ▸ 𝒰 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_unit
    apply ihiC
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_univ_empty : ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝟘 = a → eqM ▸ 𝒰 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_empty
    apply ihiC
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_univ_pi : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
   (Γ ⊢ A ∶ 𝒰) →
     (Γ ⬝ A ⊢ B ∶ 𝒰) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
             (a A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ B = a → eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               (eqM ▸ ΠA;B) = a → eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B hAU hBU ihAU ihBU m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    apply HasType.univ_pi
    · rw [←substitution_univ]
      apply ihAU
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · replace_by_conclusion ihBU
      · apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
        · rw [lift_n_substitution]
        · rw [substitution_univ]
      · apply ihBU
        repeat' rfl
        apply hsS

theorem substitution_gen_univ_sigma : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ∶ 𝒰) →
        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
            (a A_1 : Tm (m + 1 - 1 + 1)),
            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
              eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) (s S : Tm l)
              (a A_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ B = a → eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
              (a A_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                (eqM ▸ ΣA;B) = a → eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B hAU hBU ihAU ihBU m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    apply HasType.univ_sigma
    · rw [←substitution_univ]
      apply ihAU
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · replace_by_conclusion ihBU
      · apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
        · rw [lift_n_substitution]
        · rw [substitution_univ]
      · apply ihBU
        repeat' rfl
        apply hsS

theorem substitution_gen_univ_nat :
    ∀ {n : Nat} {Γ : Ctx n},
  Γ ctx →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx) →
      ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A : Tm (m + 1 - 1 + 1)),
        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
          eqM ▸ 𝒩 = a → eqM ▸ 𝒰 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_nat
    apply ihiC
    · rfl
    · apply hsS
    · rfl

theorem substitution_gen_univ_iden : ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
   (Γ ⊢ A ∶ 𝒰) →
     (Γ ⊢ a ∶ A) →
       (Γ ⊢ a' ∶ A) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = a → eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
               (a_5 A_1 : Tm (m + 1 - 1 + 1)),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a = a_5 →
                   eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a_5⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ a' = a →
                     eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a_7 A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   (eqM ▸ a ≃[A] a') = a_7 →
                     eqM ▸ 𝒰 = A_1 → (Γ_1 ⊢ s ∶ S) → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a_7⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A a a' hAU haA haA' ihAU ihaA ihaA' m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    apply HasType.univ_iden
    · rw [←substitution_univ]
      apply ihAU
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
    · apply ihaA'
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_unit_elim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
   Γ ⬝ 𝟙 ⊢ A type →
     (Γ ⊢ a ∶ A⌈⋆⌉₀) →
       (Γ ⊢ b ∶ 𝟙) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
             (A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
               (a_5 A_1 : Tm (m + 1 - 1 + 1)),
               eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ a = a_5 →
                   eqM ▸ A⌈⋆⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a A : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ b = a → eqM ▸ 𝟙 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a_7 A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A.indUnit b a = a_7 →
                     eqM ▸ A⌈b⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_7⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A a b hA haA hb1 ihA ihaA ihb1 m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_lift]
    apply HasType.unit_elim
    · replace_by_conclusion ihA
      · apply congr
        apply congr
        · rfl
        · rw [←substitution_unit]
          rw [extend_expand_context_n_substitution]
        · substitution_step
      · apply ihA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihaA
      · apply congr
        apply congr
        · rfl
        · rfl
        · simp only [lift_subst_n]
          rw [←substitution_tt]
          rw [←substitution_zero_lift]
      · apply ihaA
        repeat' rfl
        apply hsS
    · rw [←substitution_unit]
      apply ihb1
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_empty_elim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
   Γ ⬝ 𝟘 ⊢ A type →
     (Γ ⊢ b ∶ 𝟘) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
           (A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ b = a → eqM ▸ 𝟘 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A.indEmpty b = a →
                 eqM ▸ A⌈b⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A b hA hb0 ihA ihb0 m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_lift]
    apply HasType.empty_elim
    · replace_by_conclusion ihA
      · apply congr
        apply congr
        · rfl
        · rw [←substitution_empty]
          rw [extend_expand_context_n_substitution]
        · substitution_step
      · apply ihA
        repeat' rfl
        apply hsS
    · rw [←substitution_empty]
      apply ihb0
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_pi_elim : ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
   (Γ ⊢ f ∶ ΠA;B) →
     (Γ ⊢ a ∶ A) →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ f = a → (eqM ▸ ΠA;B) = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_4 A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_4 →
                 eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_4⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ f◃a = a_5 → eqM ▸ B⌈a⌉₀ = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' f A B a hfPi haA ihfPi ihaA m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_lift]
    apply HasType.pi_elim
    · rw [←substitution_pi]
      apply ihfPi
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

theorem substitution_gen_sigma_elim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
   (Γ ⊢ p ∶ ΣA;B) →
     (Γ ⬝ ΣA;B) ⊢ C type →
       (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a A_1 : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ p = a →
                 (eqM ▸ ΣA;B) = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
           (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
               (A_1 : Tm (m + 1 - 1 + 1)),
               (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ →
                 eqM ▸ C = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
             (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                 (s S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ c = a →
                     eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1 →
                       (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
               ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                 (a A_1 : Tm (m + 1 - 1 + 1)),
                 eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                   eqM ▸ A.indSigma B C c p = a →
                     eqM ▸ C⌈p⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B p C c hpSi hC hcC ihpSi ihC ihcC m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_lift]
    apply HasType.sigma_elim
    · simp [lift_subst_n]
      rw [←substitution_sigma]
      apply ihpSi
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
    · replace_by_conclusion ihcC
      · apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
          rw [lift_n_substitution]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · simp only [lift_subst_n]
          rw [subst_subst_sigma_C]
          context_info_nat_relations
          simp only [lift_n_substitution]
          rfl
      · apply ihcC
        repeat' rfl
        apply hsS

theorem substitution_gen_nat_elim :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type →
    (Γ ⊢ z ∶ A⌈𝓏⌉₀) →
      (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋) →
        (Γ ⊢ x ∶ 𝒩) →
          (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
              (A_1 : Tm (m + 1 - 1 + 1)),
              eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ →
                eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
            (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                (a A_1 : Tm (m + 1 - 1 + 1)),
                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                  eqM ▸ z = a →
                    eqM ▸ A⌈𝓏⌉₀ = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
              (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 = m + 1)
                  (s_1 S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                  eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                    eqM ▸ s = a →
                      eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1 →
                        (Γ_1 ⊢ s_1 ∶ S) → Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ a⌈s_1/ₙleq⌉ ∶ A_1⌈s_1/ₙleq⌉) →
                (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
                    (a A : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ x = a →
                        eqM ▸ 𝒩 = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉) →
                  ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                    (s_1 S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ A.indNat z s x = a →
                        eqM ▸ A⌈x⌉₀ = A_1 →
                          (Γ_1 ⊢ s_1 ∶ S) → Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ a⌈s_1/ₙleq⌉ ∶ A_1⌈s_1/ₙleq⌉ :=
  by
    intro n Γ' z x A s hA hzA hsA hxNat ihA ihzA ihsA ihxNat m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_lift]
    apply HasType.nat_elim
    · replace_by_conclusion ihA
      · apply congr
        apply congr
        · rfl
        · rw [←substitution_nat]
          rw [extend_expand_context_n_substitution]
        · substitution_step
      · apply ihA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihzA
      · apply congr
        apply congr
        · rfl
        · substitution_step
        · simp only [lift_subst_n]
          rw [←substitution_var_zero]
          rw [←substitution_zero_lift]
      · apply ihzA
        repeat' rfl
        apply hsS
    · replace_by_conclusion ihsA
      · apply congr
        apply congr
        apply congr
        · rfl
        · substitution_step
          rw [lift_n_substitution]
          rw [←substitution_nat]
          rw [extend_expand_context_n_substitution]
          rw [extend_expand_context_n_substitution]
        · substitution_step
        · context_info_nat_relations
          simp only [lift_subst_n]
          rw [←helper_subst_nat_elim]
          simp only [lift_n_substitution]
          rfl
      · apply ihsA
        repeat' rfl
        apply hsS
    · rw [←substitution_nat]
      apply ihxNat
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a a' p : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
    (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ a' ∶ A) →
          (Γ ⊢ p ∶ a ≃[A] a') →
                (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 + 1 + 1 = m + 1)
                    {s S : Tm l} (A_1 : Tm (m + 1 - 1 + 1)),
                    (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ →
                      eqM ▸ B = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type) →
                  (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1)
                      (s S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                      eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ b = a →
                          eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1 →
                            (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                        (s S : Tm l) (a_8 A_1 : Tm (m + 1 - 1 + 1)),
                        eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                          eqM ▸ a = a_8 →
                            eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_8⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                      (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                          (s S : Tm l) (a A_1 : Tm (m + 1 - 1 + 1)),
                          eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                            eqM ▸ a' = a →
                              eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                        (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                            (s S : Tm l) (a_10 A_1 : Tm (m + 1 - 1 + 1)),
                            eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                              eqM ▸ p = a_10 →
                                (eqM ▸ a ≃[A] a') = A_1 →
                                  (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_10⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
                              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
                                (s S : Tm l) (a_13 A_1 : Tm (m + 1 - 1 + 1)),
                                eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                                  eqM ▸ A.j B b a a' p = a_13 →
                                    eqM ▸ B⌈(ₛidₚ)⋄ a⋄ a'⋄ p⌉ = A_1 →
                                      (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_13⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B b a a' p hB hbB haA haA' hpId ihB ihbB ihaA ihaA' ihpId m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [subst_subst_iden_elim]
    apply HasType.iden_elim
    · context_info_nat_relations
      simp only [lift_subst_n]
      simp only [lift_n_substitution]
      simp only [←substitution_shift_id_lift]
      simp only [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw [extend_expand_context_n_substitution]
      rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      rw [←substitution_shift_id_lift]
      rw [←substitution_shift_id_lift]
      rw [weakening_shift_id]
      rw [←helper_subst_iden_propagate_subst]
      simp only [lift_n_substitution]
      rw [extend_expand_context_n_substitution]
      apply ihB
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_shift_id_lift]
      rw [subst_subst_iden_refl]
      rw [extend_expand_context_n_substitution]
      simp [lift_subst_n]
      rw [lift_n_substitution]
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
    · apply ihaA'
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl
    · rw [←substitution_iden]
      apply ihpId
      · rfl
      · rfl
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_ty_conv : ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
   (Γ ⊢ a ∶ A) →
     Γ ⊢ A ≡ B type →
       (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
           (a_3 A_1 : Tm (m + 1 - 1 + 1)),
           eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
             eqM ▸ a = a_3 → eqM ▸ A = A_1 → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_3⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉) →
         (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (A_1 A' : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ A = A_1 →
                 eqM ▸ B = A' → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ ≡ A'⌈s/ₙleq⌉ type) →
           ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
             (a_5 A : Tm (m + 1 - 1 + 1)),
             eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
               eqM ▸ a = a_5 → eqM ▸ B = A → (Γ_1 ⊢ s ∶ S) → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ∶ A⌈s/ₙleq⌉ :=
  by
    intro n Γ' a A B haA hAB ihaA ihAB m l hleq Γ Δ heqM s S t T heqΓ heqt heqT hsS
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    simp [substitute]
    apply HasType.ty_conv
    · apply ihaA
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
