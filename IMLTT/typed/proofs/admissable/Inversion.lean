import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

-- theorem pi_has_type_inversion' :
--     (Γ ⊢ ΠA;B ∶ 𝒰) → (Γ ⊢ A ∶ 𝒰) ∧ Γ ⬝ A ⊢ B ∶ 𝒰 :=
--   by
--     intro hPiV
--     apply HasType.recOn
--       (motive_1 := fun Γ _hiC => True)
--       (motive_2 := fun Γ A _hA => True)
--       (motive_3 := fun Γ x X _haA =>
--          ∀ A, ∀ B,
--          x = (.pi A B) ∧ X = 𝒰 → HasType Γ A 𝒰 ∧ HasType (Γ ⬝ A) B 𝒰)
--       (motive_4 := fun Γ A A' _hAA => True)
--       (motive_5 := fun Γ a a' A _haaA => True)
--       hPiV
--     case weak =>
--       intro n Γ i A B hvA hB ihvA ihB A' B' heq
--       have heql := And.left heq
--       cases heql
--     case univ_pi =>
--       intro n Γ A B hAU hBU ihAU ihBU A B heq
--       cases And.left heq
--       cases And.right heq
--       simp_all only [and_self]
--       -- simp_all only [and_true]
--     case ty_conv =>
--       intro n Γ i A B hvA hB ihvA ihB A' B' heq
--       cases And.left heq
--       cases And.right heq
--       apply And.intro
--       · apply HasType.ty_conv
--         rotate_left
--         · apply hB
--         · have h := ihvA A' B'
--           sorry
--
--       · sorry
--     any_goals aesop?

theorem pi_has_type_inversion :
    (Γ ⊢ ΠA;B ∶ V) → (Γ ⊢ A ∶ 𝒰) ∧ Γ ⬝ A ⊢ B ∶ 𝒰 :=
  by
    intro hPiV
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => True)
      (motive_2 := fun Γ A _hA => True)
      (motive_3 := fun Γ x X _haA =>
         ∀ A, ∀ B, ∀ V,
         x = (.pi A B) ∧ X = V → HasType Γ A 𝒰 ∧ HasType (Γ ⬝ A) B 𝒰)
      (motive_4 := fun Γ A A' _hAA => True)
      (motive_5 := fun Γ a a' A _haaA => True)
      hPiV
    case weak =>
      intro n Γ i A B hvA hB ihvA ihB A' B' V heq
      have heql := And.left heq
      cases heql
    case ty_conv =>
      intro n Γ a A B haA hAB ihaA ihAB A' B' V heq
      cases And.left heq
      cases And.right heq
      apply ihaA
      apply And.intro
      · rfl
      · rfl
    any_goals aesop

theorem pi_is_type_inversion :
    Γ ⊢ ΠA;B type → Γ ⊢ A type ∧ Γ ⬝ A ⊢ B type :=
  by
    intro hPi
    match hPi with
    | .pi_form hA hB =>
      apply And.intro hA hB
    | .univ_elim hPiU =>
      have hAUBU := pi_has_type_inversion hPiU
      apply And.intro
      · apply IsType.univ_elim (And.left hAUBU)
      · apply IsType.univ_elim (And.right hAUBU)

theorem sigma_has_type_inversion :
    (Γ ⊢ ΣA;B ∶ V) → (Γ ⊢ A ∶ 𝒰) ∧ Γ ⬝ A ⊢ B ∶ 𝒰 :=
  by
    intro hSiV
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ x X _haA =>
         ∀ A, ∀ B, ∀ V,
         x = (.sigma A B) ∧ X = V → HasType Γ A 𝒰 ∧ HasType (Γ ⬝ A) B 𝒰)
      (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
      (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
      hSiV
    case weak =>
      intro n Γ i A B hvA hB ihvA ihB A' B' V heq
      have heql := And.left heq
      cases heql
    case weak_eq =>
      intro n Γ i A B hvvA hB ihvvA ihB
      apply IsEqualTerm.weak_eq
      · apply hvvA
      · apply hB
    any_goals aesop

theorem sigma_is_type_inversion :
    Γ ⊢ ΣA;B type → Γ ⊢ A type ∧ Γ ⬝ A ⊢ B type :=
  by
    intro hSi
    match hSi with
    | .sigma_form hA hB =>
      apply And.intro hA hB
    | .univ_elim hSiU =>
      have hAUBU := sigma_has_type_inversion hSiU
      apply And.intro
      · apply IsType.univ_elim (And.left hAUBU)
      · apply IsType.univ_elim (And.right hAUBU)

set_option maxHeartbeats 1000000

theorem iden_has_type_inversion :
    (Γ ⊢ a ≃[A] a' ∶ V) → (Γ ⊢ A ∶ 𝒰) ∧ (Γ ⊢ a ∶ A) ∧ Γ ⊢ a' ∶ A :=
  by
    intro hIdV
    apply HasType.recOn
      (motive_1 := fun Γ _hiC => IsCtx Γ)
      (motive_2 := fun Γ A _hA => IsType Γ A)
      (motive_3 := fun Γ x X _haA =>
         ∀ A, ∀ a, ∀ a', ∀ V,
         x = (.iden A a a') ∧ X = V → HasType Γ A 𝒰 ∧ HasType Γ a A ∧ HasType Γ a' A)
      (motive_4 := fun Γ A A' _hAA => IsEqualType Γ A A')
      (motive_5 := fun Γ a a' A _haaA => IsEqualTerm Γ a a' A)
      hIdV
    case ty_conv =>
      intro n Γ a A B _haA _hAB ihaA _ihAB
      intro A a a' V h1
      apply ihaA
      apply And.intro
      · apply (And.left h1)
      · rfl
    case weak =>
      intro n Γ i A B hvA hB ihvA ihB A' a a' V heq
      have heql := And.left heq
      cases heql
    case weak_eq =>
      intro n Γ i A B hvvA hB ihvvA ihB
      apply IsEqualTerm.weak_eq
      · apply hvvA
      · apply hB
    any_goals aesop

theorem iden_is_type_inversion :
    Γ ⊢ a ≃[A] a' type → (Γ ⊢ A type) ∧ (Γ ⊢ a ∶ A) ∧ Γ ⊢ a' ∶ A :=
  by
    intro hId
    match hId with
    | .iden_form hA haA haA' => apply And.intro hA (And.intro haA haA')
    | .univ_elim hIdU =>
      have h1 := iden_has_type_inversion hIdU
      apply And.intro (IsType.univ_elim (And.left h1)) (And.right h1)
