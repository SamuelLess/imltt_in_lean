import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

theorem functionality_typing_var :
  ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
  Γ ⊢ A type
  → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : x = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
        (eqM : x = m + 1),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = T
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
  → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : x + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
        (eqM : x + 1 = m + 1),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ v(0) = t
      → eqM ▸ A⌊↑ₚidₚ⌋ = T
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A hA ihA
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases Ξ with
      | start =>
        cases heqΓ
        apply And.right ihA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      | expand Ξ' A' =>
        cases heqΓ
        cases n with
        | zero =>
          have hneq := gen_ctx_neq Ξ'
          omega
        | succ n' =>
          apply And.left ihA
          · apply hssS
          · apply hsS
          · apply hsS'
          rotate_left
          · apply n'
          · apply Ξ'
          · rfl
          · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqt
      cases heqT
      cases n with
      | zero =>
        simp only [substitute]
        simp only [n_substitution]
        simp only [substitute_var]
        rw [substitution_conv_zero]
        rw [substitution_shift_substitute_zero]
        cases Δ with
        | start =>
          cases heqΓ
          apply hssS
        | expand Δ' T =>
          have h1 := gen_ctx_leq Δ'
          omega
      | succ n' =>
        simp only [substitute]
        simp only [n_substitution]
        split
        case isTrue hT =>
          simp only [substitute_var]
          simp only [substitution_shift_id_lift]
          cases Δ with
          | start =>
            omega
          | expand Δ' T =>
            rw [←extend_expand_context] at heqΓ
            cases heqΓ
            apply IsEqualTerm.var_eq
            apply And.left (And.right substitution)
            · apply hA
            · apply hsS
        case isFalse hF =>
          simp []
          split
          case h_1 =>
            cases Δ with
            | start =>
              cases heqΓ
              apply hssS
            | expand Δ' T =>
              have h1 := gen_ctx_leq Δ'
              omega
          case h_2 h =>
            cases h

theorem functionality_typing_weak :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ∶ A)
    → Γ ⊢ B type
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : x = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : x = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ v(i) = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : x = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
          (eqM : x = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ B = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : x + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : x + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ B = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ v(i)⌊↑ₚidₚ⌋ = t
        → eqM ▸ A⌊↑ₚidₚ⌋ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n x Γ' A B hvA hB ihvA ihB
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases Ξ with
      | start =>
        cases heqΓ
        apply And.right ihB
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      | expand Ξ' A' =>
        cases heqΓ
        cases n with
        | zero =>
          have hneq := gen_ctx_neq Ξ'
          omega
        | succ n' =>
          apply And.left ihB
          · apply hssS
          · apply hsS
          · apply hsS'
          rotate_left
          · apply n'
          · apply Ξ'
          · rfl
          · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqt
      cases heqT
      simp_all
      cases n
      case zero =>
        simp only [n_substitution]
        simp only [substitution_conv_zero]
        simp only [substitution_shift_substitute_zero]
        cases Δ with
        | start =>
          simp [expand_ctx]
          cases heqΓ
          apply defeq_refl_term hvA
        | expand Δ' T =>
          have h := gen_ctx_neq Δ'
          omega
      case succ n' =>
        simp [n_substitution]
        split
        case isTrue hT =>
          simp only [substitution_shift_id_lift]
          cases Δ with
          | start =>
            omega
          | expand Δ' T =>
            cases heqΓ
            have h := gen_ctx_leq Δ'
            simp only [substitute_into_gen_ctx]
            simp only [expand_ctx]
            apply weakening_term_eq
            · simp only [←substitution_conv_var]
              apply And.right ihvA
              · apply hssS
              · apply hsS
              · apply hsS'
              · rfl
              · rfl
              · rfl
              · rfl
            · apply And.left (And.right substitution)
              · apply hB
              · apply hsS
        case isFalse hF =>
          rw [substitution_conv_zero]
          rw [substitution_shift_substitute_zero]
          cases Δ with
          | start =>
            cases heqΓ
            apply defeq_refl_term hvA
          | expand Δ' T =>
            have h := gen_ctx_leq Δ'
            omega

theorem functionality_typing_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ ⋆ = t
        → eqM ▸ 𝟙 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply ihiC
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.unit_intro_eq
      simp_all
      cases Δ
      case start =>
        exact ctx_decr hiC
      case expand Δ' T =>
        apply And.left substitution
        · apply hiC
        · apply hsS

theorem functionality_typing_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ∶ B)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ b = t
        → eqM ▸ B = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
         (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → (eqM ▸ λA; b) = t
        → (eqM ▸ ΠA;B) = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A b B hbB ihbB
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihbB
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k + 1
      · apply Ξ ⊙ A
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.pi_intro_eq
      · simp only [lift_subst_n]
        rw [lift_n_substitution]
        rw [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        apply And.right ihbB
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · apply And.left ihbB
        · apply hssS
        · apply hsS
        · apply hsS'
        rotate_left
        · apply m + 1
        · apply CtxGen.start
        · rfl
        · rfl

theorem functionality_typing_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ∶ A)
    → (Γ ⊢ b ∶ B⌈a⌉₀)
    → Γ ⬝ A ⊢ B type
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ b = t
        → eqM ▸ B⌈a⌉₀ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
          (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ B = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a&b = t
        → (eqM ▸ ΣA;B) = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' a A b B haA hbB hB ihaA ihbB ihB
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihaA
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.sigma_intro_eq
      · apply And.right ihaA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · simp only [lift_subst_n]
        rw [←substitution_zero_lift]
        apply And.right ihbB
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · simp only [lift_subst_n]
        rw [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        apply And.left (And.right substitution)
        · apply hB
        · apply hsS

theorem functionality_typing_nat_zero_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ 𝓏 = t
        → eqM ▸ 𝒩 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply ihiC
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.nat_zero_intro_eq
      cases Δ
      case start =>
        exact ctx_decr hiC
      case expand Δ' T =>
        apply And.left substitution
        · apply hiC
        · apply hsS

theorem functionality_typing_nat_succ_intro :
    ∀ {n : Nat} {Γ : Ctx n} {x : Tm n},
    (Γ ⊢ x ∶ 𝒩)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ x = t
        → eqM ▸ 𝒩 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ 𝓈(x) = t
        → eqM ▸ 𝒩 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' x hxNat ihxNat
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihxNat
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp [substitute]
      apply IsEqualTerm.nat_succ_intro_eq
      rw [←substitution_nat]
      apply And.right ihxNat
      · apply hssS
      · apply hsS
      · apply hsS'
      repeat' rfl

theorem functionality_typing_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
    Γ ⊢ A type
    → (Γ ⊢ a ∶ A)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A.refl a = t
        → (eqM ▸ a ≃[A] a) = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A a hA haA ihA ihaA
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihaA
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp [substitute]
      apply IsEqualTerm.iden_intro_eq
      · apply And.right ihA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · apply And.right ihaA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ 𝟙 = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply ihiC
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_unit_eq
      apply And.left substitution
      · apply hiC
      · apply hsS

theorem functionality_typing_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ 𝟘 = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply ihiC
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_empty_eq
      apply And.left substitution
      · apply hiC
      · apply hsS

theorem functionality_typing_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ∶ 𝒰)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ B = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → (eqM ▸ ΠA;B) = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B hAU hBU ihAU ihBU
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihAU
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_pi_eq
      · rw [←substitution_univ]
        apply And.right ihAU
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · simp only [lift_subst_n]
        rw [lift_n_substitution]
        rw [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        rw [←substitution_univ]
        apply And.right ihBU
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ∶ 𝒰)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ B = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → (eqM ▸ ΣA;B) = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B hAU hBU ihAU ihBU
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihAU
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.univ_sigma_eq
      · rw [←substitution_univ]
        apply And.right ihAU
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · simp only [lift_subst_n]
        rw [lift_n_substitution]
        rw [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        rw [←substitution_univ]
        apply And.right ihBU
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_univ_nat :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
        (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
        (eqM : n = m + 1),
      (Γ_1 ⊢ s ≡ s' ∶ S)
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊢ s' ∶ S)
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ 𝒩 = t
      → eqM ▸ 𝒰 = T
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' hiC ihiC
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply ihiC
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp [substitute]
      apply IsEqualTerm.univ_nat_eq
      apply And.left substitution
      · apply hiC
      · apply hsS

theorem functionality_typing_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a' = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → (eqM ▸ a ≃[A] a') = t
        → eqM ▸ 𝒰 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A a a' hAU haA haA' ihAU ihaA ihaA'
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihAU
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp [substitute]
      apply IsEqualTerm.univ_iden_eq
      · rw [←substitution_univ]
        apply And.right ihAU
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · apply And.right ihaA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · apply And.right ihaA'
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_unit_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type
    → (Γ ⊢ a ∶ A⌈⋆⌉₀)
    → (Γ ⊢ b ∶ 𝟙)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
          (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = t
        → eqM ▸ A⌈⋆⌉₀ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ b = t
        → eqM ▸ 𝟙 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A.indUnit b a = t
        → eqM ▸ A⌈b⌉₀ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A a b hA haA hb1 ihA ihaA ihb1
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihaA
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp only [substitution_zero_lift]
      apply IsEqualTerm.unit_elim_eq
      · simp only [lift_subst_n]
        simp only [lift_n_substitution]
        rw [←substitution_unit]
        rw [extend_expand_context_n_substitution]
        apply And.right ihA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · simp only [lift_subst_n]
        rw [←substitution_tt]
        rw [←substitution_zero_lift]
        apply And.right ihaA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · rw [←substitution_unit]
        apply And.right ihb1
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
    Γ ⬝ 𝟘 ⊢ A type
    → (Γ ⊢ b ∶ 𝟘)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
          (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ b = t
        → eqM ▸ 𝟘 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A.indEmpty b = t
        → eqM ▸ A⌈b⌉₀ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A b hA hb0 ihA ihb0
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihb0
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp only [substitution_zero_lift]
      apply IsEqualTerm.empty_elim_eq
      · simp only [lift_subst_n]
        simp only [lift_n_substitution]
        rw [←substitution_empty]
        rw [extend_expand_context_n_substitution]
        apply And.right ihA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · rw [←substitution_empty]
        apply And.right ihb0
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
    (Γ ⊢ f ∶ ΠA;B)
    → (Γ ⊢ a ∶ A)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ f = t
        → (eqM ▸ ΠA;B) = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ f◃a = t
        → eqM ▸ B⌈a⌉₀ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' f A B a hfPi haA ihfPi ihaA
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihfPi
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp only [substitution_zero_lift]
      apply IsEqualTerm.pi_elim_eq
      · rw [←substitution_pi]
        apply And.right ihfPi
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · apply And.right ihaA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_sigma_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
    (Γ ⬝ ΣA;B) ⊢ C type
    → (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
    → (Γ ⊢ p ∶ ΣA;B)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
          (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ C = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n + 1 + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ c = t
        → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ p = t
        → (eqM ▸ ΣA;B) = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A.indSigma B C c p = t
        → eqM ▸ C⌈p⌉₀ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B p C c hC hcC hpSi ihC ihcC ihpSi
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihpSi
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      simp only [substitution_zero_lift]
      apply IsEqualTerm.sigma_elim_eq
      · simp [lift_subst_n]
        rw [←substitution_sigma]
        rw [lift_n_substitution]
        rw [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        apply And.right ihC
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · simp only [lift_subst_n]
        rw [helper_substitution_sigma_elim_C]
        simp only [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        rw [extend_expand_context_n_substitution]
        apply And.right ihcC
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · apply And.left ihcC
        · apply hssS
        · apply hsS
        · apply hsS'
        rotate_left
        · apply m + 1 + 1
        · apply CtxGen.start ⊙ B
        · rfl
        · rfl
      · simp only [lift_subst_n]
        simp only [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        apply And.left ihcC
        · apply hssS
        · apply hsS
        · apply hsS'
        rotate_left
        · apply m + 1 + 1
        · apply CtxGen.start
        · rfl
        · rfl
      · simp [lift_subst_n]
        rw [←substitution_sigma]
        apply And.right ihpSi
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_nat_elim :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ∶ 𝒩)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
          (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ z = t
        → eqM ▸ A⌈𝓏⌉₀ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s_1 s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n + 1 + 1 = m + 1),
        (Γ_1 ⊢ s_1 ≡ s' ∶ S)
        → (Γ_1 ⊢ s_1 ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ s = t
        → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = T
        → Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ t⌈s_1/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s_1/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM :n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ x = t
        → eqM ▸ 𝒩 = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s_1 s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s_1 ≡ s' ∶ S)
        → (Γ_1 ⊢ s_1 ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A.indNat z s x = t
        → eqM ▸ A⌈x⌉₀ = T
        → Γ_1 ⊗ ⌈s_1⌉(Δ w/Nat.le_refl l) ⊢ t⌈s_1/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s_1/ₙleq⌉ :=
  by
    intro n Γ' z x A s hA hzA hsA hxNat ihA ihzA ihsA ihxNat
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihxNat
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      rw [substitution_zero_lift]
      apply IsEqualTerm.nat_elim_eq
      · simp only [lift_subst_n]
        simp only [lift_n_substitution]
        rw [←substitution_nat]
        rw [extend_expand_context_n_substitution]
        apply And.right ihA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · simp only [lift_subst_n]
        rw [←substitution_var_zero]
        rw [←substitution_zero_lift]
        apply And.right ihzA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · rw [←substitution_nat]
        rw [extend_expand_context_n_substitution]
        simp only [lift_subst_n]
        rw [←helper_substitution_nat_elim]
        simp only [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        apply And.right ihsA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · rw [←substitution_nat]
        apply And.right ihxNat
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a a' p : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
    → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → (Γ ⊢ p ∶ a ≃[A] a')
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n + 1 + 1 + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (T : Tm (m + 1)) (eqM : n + 1 + 1 + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ B = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1))
          (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n + 1 = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n + 1 = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ b = t
        → eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1))
          (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1))
          (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a' = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1))
          (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ p = t
        → (eqM ▸ a ≃[A] a') = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1))
          (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l)
          (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A.j B b a a' p = t
        → eqM ▸ B⌈(ₛidₚ)⋄ a⋄ a'⋄ p⌉ = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' A B b a a' p hB hbB haA haA' hpId ihB ihbB ihaA ihaA' ihpId
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihpId
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      rw [helper_substitution_iden_B]
      apply IsEqualTerm.iden_elim_eq
      · simp only [lift_subst_n]
        simp only [lift_n_substitution]
        simp only [←substitution_shift_id_lift]
        simp only [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        rw [extend_expand_context_n_substitution]
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        rw [←substitution_shift_id_lift]
        rw [←substitution_shift_id_lift]
        rw [weakening_shift_id]
        rw [←helper_substitution_iden_propagate_subst]
        simp only [lift_n_substitution]
        rw [extend_expand_context_n_substitution]
        apply And.right ihB
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · rw [←substitution_shift_id_lift]
        rw [helper_substitution_iden_B_refl]
        rw [extend_expand_context_n_substitution]
        simp [lift_subst_n]
        rw [lift_n_substitution]
        rw [lift_n_substitution]
        apply And.right ihbB
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · apply And.left ihB
        · apply hssS
        · apply hsS
        · apply hsS'
        rotate_left
        · apply m + 1 + 1 + 1
        · apply CtxGen.start ⊙ A⌊↑ₚidₚ⌋ ⊙ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)
        · rfl
        · rfl
      · apply And.right ihaA
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl
      · apply IsEqualTerm.ty_conv_eq
        · apply And.right ihaA'
          · apply hssS
          · apply hsS
          · apply hsS'
          repeat' rfl
        · apply And.left ihB
          · apply hssS
          · apply hsS
          · apply hsS'
          rotate_left
          · apply m + 1 + 1 + 1
          · apply CtxGen.start ⊙ A⌊↑ₚidₚ⌋ ⊙ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)
          · rfl
          · rfl
      · rw [←substitution_iden]
        apply And.right ihpId
        · apply hssS
        · apply hsS
        · apply hsS'
        repeat' rfl

theorem functionality_typing_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
    (Γ ⊢ a ∶ A)
    → Γ ⊢ A ≡ B type
    → ((∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = t
        → eqM ▸ A = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉)
    → Γ ⊢ A ≡ B type
    → (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
          (eqM : n = m + 1),
        (Γ_1 ⊢ s ≡ s' ∶ S)
        → (Γ_1 ⊢ s ∶ S)
        → (Γ_1 ⊢ s' ∶ S)
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = t
        → eqM ▸ B = T
        → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉ :=
  by
    intro n Γ' a A B haA hAB ihaA ihAB
    apply And.intro
    · intro m l k hleq Γ Δ Ξ heqM s s' S T hssS hsS hsS' heqΓ
      cases heqM
      cases heqΓ
      apply And.left ihaA
      · apply hssS
      · apply hsS
      · apply hsS'
      rotate_left
      · apply k
      · apply Ξ
      · rfl
      · rfl
    · intro m l hleq Γ Δ s s' S t T heqM hssS hsS hsS' heqΓ heqt heqT
      cases heqM
      cases heqΓ
      cases heqt
      cases heqT
      apply IsEqualTerm.ty_conv_eq
      · apply And.right ihaA
        · exact hssS
        · exact hsS
        · exact hsS'
        repeat' rfl
      · exact substitution_general_type_eq hAB hsS
