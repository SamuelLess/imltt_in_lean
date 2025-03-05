import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.FunctionalityTyping
import IMLTT.typed.proofs.admissable.ContextConv
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.boundary.Helpers

theorem boundary_var_eq :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type → Γ ⊢ A type → (Γ ⬝ A ⊢ v(0) ∶ A⌊↑ₚidₚ⌋) ∧ (Γ ⬝ A ⊢ v(0) ∶ A⌊↑ₚidₚ⌋) ∧ Γ ⬝ A ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n Γ A hA ihA
    apply And.intro
    · apply HasType.var hA
    · apply And.intro
      · apply HasType.var hA
      · apply weakening_type hA hA

theorem boundary_weak_eq :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ≡ v(i) ∶ A) →
    Γ ⊢ B type →
    (Γ ⊢ v(i) ∶ A) ∧ (Γ ⊢ v(i) ∶ A) ∧ Γ ⊢ A type →
    Γ ⊢ B type → (Γ ⬝ B ⊢ v(i)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋) ∧ (Γ ⬝ B ⊢ v(i)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋) ∧ Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n x Γ A B hvvA hB ihvvA ihB
    apply And.intro
    · apply HasType.weak
      · apply And.left ihvvA
      · apply ihB
    · apply And.intro
      · apply HasType.weak
        · apply And.left ihvvA
        · apply ihB
      · apply weakening_type
        · apply And.right (And.right ihvvA)
        · apply ihB

theorem boundary_unit_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a : Tm n},
    Γ ⬝ 𝟙 ⊢ A type →
    (Γ ⊢ a ∶ A⌈⋆⌉₀) → Γ ⬝ 𝟙 ⊢ A type → Γ ⊢ A⌈⋆⌉₀ type → (Γ ⊢ A.indUnit ⋆ a ∶ A⌈⋆⌉₀) ∧ (Γ ⊢ a ∶ A⌈⋆⌉₀) ∧ Γ ⊢ A⌈⋆⌉₀ type :=
  by
    intro n Γ A a hA haA ihA ihaA
    repeat' apply And.intro
    · apply HasType.unit_elim
      · apply hA
      · apply haA
      · apply HasType.unit_intro
        apply boundary_ctx_term haA
    · apply haA
    · apply ihaA

theorem boundary_pi_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)} {a : Tm n},
    (Γ ⬝ A ⊢ b ∶ B) →
    (Γ ⊢ a ∶ A) → Γ ⬝ A ⊢ B type → Γ ⊢ A type → (Γ ⊢ (λA; b)◃a ∶ B⌈a⌉₀) ∧ (Γ ⊢ b⌈a⌉₀ ∶ B⌈a⌉₀) ∧ Γ ⊢ B⌈a⌉₀ type :=
  by
    intro n Γ A b B a hbB haA ihbB ihaA
    repeat' apply And.intro
    · apply HasType.pi_elim
      · apply HasType.pi_intro
        apply hbB
      · apply haA
    · apply substitution_term
      · apply haA
      · apply hbB
    · apply substitution_type
      · apply haA
      · apply ihbB

theorem boundary_sigma_first_comp :
    ∀ {n : Nat} {Γ : Ctx n} {a b A : Tm n} {B : Tm (n + 1)},
  (Γ ⊢ a ∶ A) →
    (Γ ⊢ b ∶ B⌈a⌉₀) →
      Γ ⊢ ΣA;B type → Γ ⊢ A type → Γ ⊢ B⌈a⌉₀ type → Γ ⊢ ΣA;B type → (Γ ⊢ π₁ a&b ∶ A) ∧ (Γ ⊢ a ∶ A) ∧ Γ ⊢ A type :=
  by
    intro n Γ a b A B haA hbB hSi ihaA ihbB ihSi
    repeat' apply And.intro
    · apply HasType.sigma_first
      apply HasType.sigma_intro
      · apply haA
      · apply hbB
      · have h := sigma_is_type_inversion hSi
        apply And.right h
    · apply haA
    · apply ihaA

theorem boundary_sigma_second_comp :
    ∀ {n : Nat} {Γ : Ctx n} {a b A : Tm n} {B : Tm (n + 1)},
  (Γ ⊢ a ∶ A) →
    (Γ ⊢ b ∶ B⌈a⌉₀) →
      Γ ⊢ ΣA;B type →
        Γ ⊢ A type →
          Γ ⊢ B⌈a⌉₀ type → Γ ⊢ ΣA;B type → (Γ ⊢ π₂ a&b ∶ B⌈π₁ a&b⌉₀) ∧ (Γ ⊢ b ∶ B⌈π₁ a&b⌉₀) ∧ Γ ⊢ B⌈π₁ a&b⌉₀ type :=
  by
    intro n Γ a b A B haA hbB hSi ihaA ihbB ihSi
    repeat' apply And.intro
    · apply HasType.sigma_second
      apply HasType.sigma_intro
      · apply haA
      · apply hbB
      · have h := sigma_is_type_inversion hSi
        apply And.right h
    · apply HasType.ty_conv
      · apply hbB
      · have h := sigma_is_type_inversion hSi
        apply functionality_typing_type
        · apply And.right h
        · apply IsEqualTerm.term_symm
          apply IsEqualTerm.sigma_first_comp
          · apply haA
          · apply hbB
          · apply hSi
        · apply haA
        · apply HasType.sigma_first
          apply HasType.sigma_intro
          · apply haA
          · apply hbB
          · apply And.right h
    · have h := sigma_is_type_inversion hSi
      apply substitution_type
      · apply HasType.sigma_first
        apply HasType.sigma_intro
        · apply haA
        · apply hbB
        · apply And.right h
      · apply And.right h

theorem boundary_iden_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
    (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
      (Γ ⊢ a ∶ A) →
        Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
          (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
            Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
              Γ ⊢ A type →
                Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
                  (Γ ⊢ A.j B b a a (A.refl a) ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) ∧
                    (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) ∧ Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type
 :=
  by
    intro n Γ A B b a hB hbB haA hBa ihB ihbB ihaA ihBa
    repeat' apply And.intro
    · apply HasType.iden_elim
      · apply hB
      · apply hbB
      · apply haA
      · apply haA
      · apply HasType.iden_intro
        · apply ihaA
        · apply haA
      · apply hBa
      · apply ihbB
    · apply hbB
    · apply ihbB

theorem boundary_unit_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → (Γ ⊢ ⋆ ∶ 𝟙) ∧ (Γ ⊢ ⋆ ∶ 𝟙) ∧ Γ ⊢ 𝟙 type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · apply HasType.unit_intro hiC
    · apply HasType.unit_intro hiC
    · apply IsType.unit_form hiC

theorem boundary_unit_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
    Γ ⬝ 𝟙 ⊢ A ≡ A' type →
    (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀) →
    (Γ ⊢ b ≡ b' ∶ 𝟙) →
    Γ ⬝ 𝟙 ⊢ A type ∧ Γ ⬝ 𝟙 ⊢ A' type →
    (Γ ⊢ a ∶ A⌈⋆⌉₀) ∧ (Γ ⊢ a' ∶ A⌈⋆⌉₀) ∧ Γ ⊢ A⌈⋆⌉₀ type →
    (Γ ⊢ b ∶ 𝟙) ∧ (Γ ⊢ b' ∶ 𝟙) ∧ Γ ⊢ 𝟙 type →
    (Γ ⊢ A.indUnit b a ∶ A⌈b⌉₀) ∧ (Γ ⊢ A'.indUnit b' a' ∶ A⌈b⌉₀) ∧ Γ ⊢ A⌈b⌉₀ type :=
  by
    intro n Γ A A' a a' b b' hAA haaA hbb1 ihAA ihaaA ihbb1
    repeat' apply And.intro
    · apply HasType.unit_elim
      · apply And.left ihAA
      · apply And.left ihaaA
      · apply And.left ihbb1
    · apply HasType.ty_conv
      · apply HasType.unit_elim
        · apply And.right ihAA
        · apply HasType.ty_conv
          · apply And.left (And.right ihaaA)
          · apply substitution_type_eq
            · apply HasType.unit_intro (boundary_ctx_term_eq haaA)
            · apply hAA
        · apply And.left (And.right ihbb1)
      · have hAA' := substitution_type_eq (And.left (And.right ihbb1)) (hAA)
        apply IsEqualType.type_trans
        · apply IsEqualType.type_symm hAA'
        · apply functionality_typing_type
          · apply And.left ihAA
          · apply IsEqualTerm.term_symm hbb1
          · apply And.left (And.right ihbb1)
          · apply And.left ihbb1
    · apply substitution_type
      · apply And.left ihbb1
      · apply And.left ihAA

theorem boundary_empty_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
    Γ ⬝ 𝟘 ⊢ A ≡ A' type →
    (Γ ⊢ b ≡ b' ∶ 𝟘) →
    Γ ⬝ 𝟘 ⊢ A type ∧ Γ ⬝ 𝟘 ⊢ A' type →
    (Γ ⊢ b ∶ 𝟘) ∧ (Γ ⊢ b' ∶ 𝟘) ∧ Γ ⊢ 𝟘 type →
    (Γ ⊢ A.indEmpty b ∶ A⌈b⌉₀) ∧ (Γ ⊢ A'.indEmpty b' ∶ A⌈b⌉₀) ∧ Γ ⊢ A⌈b⌉₀ type :=
  by
    intro n Γ A A' b b' hAA hbb0 ihAA ihbb0
    repeat' apply And.intro
    · apply HasType.empty_elim
      · apply And.left ihAA
      · apply And.left ihbb0
    · apply HasType.ty_conv
      · apply HasType.empty_elim
        · apply And.right ihAA
        · apply HasType.ty_conv
          · apply And.left (And.right ihbb0)
          · apply IsEqualType.empty_form_eq (boundary_ctx_term_eq hbb0)
      · have hAA' := substitution_type_eq (And.left (And.right ihbb0)) (hAA)
        apply IsEqualType.type_trans
        · apply IsEqualType.type_symm hAA'
        · apply functionality_typing_type
          · apply And.left ihAA
          · apply IsEqualTerm.term_symm hbb0
          · apply And.left (And.right ihbb0)
          · apply And.left ihbb0
    · apply substitution_type
      · apply And.left ihbb0
      · apply And.left ihAA

theorem boundary_pi_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B) →
    Γ ⊢ A ≡ A' type →
    (Γ ⬝ A ⊢ b ∶ B) ∧ (Γ ⬝ A ⊢ b' ∶ B) ∧ Γ ⬝ A ⊢ B type →
    Γ ⊢ A type ∧ Γ ⊢ A' type → (Γ ⊢ λA; b ∶ ΠA;B) ∧ (Γ ⊢ λA'; b' ∶ ΠA;B) ∧ Γ ⊢ ΠA;B type :=
  by
    intro n Γ A A' b b' B hbbB hAA ihbbB ihAA
    repeat' apply And.intro
    · apply HasType.pi_intro
      apply And.left ihbbB
    · apply HasType.ty_conv
      · apply HasType.pi_intro
        · apply context_conversion_term
          · apply And.right ihAA
          · apply hAA
          · apply And.left (And.right ihbbB)
      · apply IsEqualType.pi_form_eq
        · apply IsEqualType.type_symm hAA
        · apply defeq_refl_type
          apply context_conversion_type
          · apply And.right ihAA
          · apply hAA
          · apply And.right (And.right ihbbB)
    · apply IsType.pi_form
      · apply And.left ihAA
      · apply And.right (And.right ihbbB)

theorem boundary_pi_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {f f' A : Tm n} {B : Tm (n + 1)} {a a' : Tm n},
    (Γ ⊢ f ≡ f' ∶ ΠA;B) →
    (Γ ⊢ a ≡ a' ∶ A) →
    (Γ ⊢ f ∶ ΠA;B) ∧ (Γ ⊢ f' ∶ ΠA;B) ∧ Γ ⊢ ΠA;B type →
    (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type → (Γ ⊢ f◃a ∶ B⌈a⌉₀) ∧ (Γ ⊢ f'◃a' ∶ B⌈a⌉₀) ∧ Γ ⊢ B⌈a⌉₀ type :=
  by
    intro n Γ f f' A B a a' hffpi haaA ihffPi ihaaA
    repeat' apply And.intro
    · apply HasType.pi_elim
      · apply And.left ihffPi
      · apply And.left ihaaA
    · apply HasType.ty_conv
      · apply HasType.pi_elim
        · apply And.left (And.right ihffPi)
        · apply And.left (And.right ihaaA)
      · have hPiInv := pi_is_type_inversion (And.right (And.right ihffPi))
        apply functionality_typing_type
        · apply And.right hPiInv
        · apply IsEqualTerm.term_symm haaA
        · apply And.left (And.right ihaaA)
        · apply And.left (ihaaA)
    · apply substitution_type
      · apply And.left ihaaA
      · have hPiInv := pi_is_type_inversion (And.right (And.right ihffPi))
        apply And.right hPiInv

theorem boundary_sigma_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ≡ a' ∶ A) →
    (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀) →
      Γ ⬝ A ⊢ B type →
        (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type →
          (Γ ⊢ b ∶ B⌈a⌉₀) ∧ (Γ ⊢ b' ∶ B⌈a⌉₀) ∧ Γ ⊢ B⌈a⌉₀ type →
            Γ ⬝ A ⊢ B type → (Γ ⊢ a&b ∶ ΣA;B) ∧ (Γ ⊢ a'&b' ∶ ΣA;B) ∧ Γ ⊢ ΣA;B type :=
  by
    intro n Γ a a' A b b' B haaA hbbB hB ihaaA ihbbB ihB
    repeat' apply And.intro
    · apply HasType.sigma_intro
      · apply And.left ihaaA
      · apply And.left ihbbB
      · apply hB
    · apply HasType.ty_conv
      · apply HasType.sigma_intro
        · apply And.left (And.right ihaaA)
        · apply HasType.ty_conv
          · apply And.left (And.right ihbbB)
          · apply functionality_typing_type
            · apply hB
            · apply haaA
            · apply And.left ihaaA
            · apply And.left (And.right ihaaA)
        · apply hB
      · apply defeq_refl_type
        apply IsType.sigma_form
        · apply And.right (And.right ihaaA)
        · apply hB
    · apply IsType.sigma_form
      · apply And.right (And.right ihaaA)
      · apply hB

theorem boundary_sigma_first_eq :
    ∀ {n : Nat} {Γ : Ctx n} {p p' A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ p ≡ p' ∶ ΣA;B) → (Γ ⊢ p ∶ ΣA;B) ∧ (Γ ⊢ p' ∶ ΣA;B) ∧ Γ ⊢ ΣA;B type → (Γ ⊢ π₁ p ∶ A) ∧ (Γ ⊢ π₁ p' ∶ A) ∧ Γ ⊢ A type :=
  by
    intro n Γ p p' A B hppSi ihppSi
    repeat' apply And.intro
    · apply HasType.sigma_first
      apply And.left ihppSi
    · apply HasType.sigma_first
      apply And.left (And.right ihppSi)
    · have h := sigma_is_type_inversion (And.right (And.right ihppSi))
      apply And.left h

theorem boundary_sigma_second_eq :
    ∀ {n : Nat} {Γ : Ctx n} {p p' A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ p ≡ p' ∶ ΣA;B) →
    (Γ ⊢ p ∶ ΣA;B) ∧ (Γ ⊢ p' ∶ ΣA;B) ∧ Γ ⊢ ΣA;B type →
      (Γ ⊢ π₂ p ∶ B⌈π₁ p⌉₀) ∧ (Γ ⊢ π₂ p' ∶ B⌈π₁ p⌉₀) ∧ Γ ⊢ B⌈π₁ p⌉₀ type :=
  by
    intro n Γ p p' A B hppSi ihppSi
    repeat' apply And.intro
    · apply HasType.sigma_second
      apply And.left ihppSi
    · apply HasType.ty_conv
      · apply HasType.sigma_second
        apply And.left (And.right ihppSi)
      · have h := sigma_is_type_inversion (And.right (And.right ihppSi))
        apply functionality_typing_type
        · apply And.right h
        · apply IsEqualTerm.term_symm
          apply IsEqualTerm.sigma_first_eq
          apply hppSi
        · apply HasType.sigma_first
          apply And.left (And.right ihppSi)
        · apply HasType.sigma_first
          apply And.left ihppSi
    · have h := sigma_is_type_inversion (And.right (And.right ihppSi))
      apply substitution_type
      · apply HasType.sigma_first
        apply And.left ihppSi
      · apply And.right h

theorem boundary_iden_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
    Γ ⊢ A ≡ A' type →
    (Γ ⊢ a ≡ a' ∶ A) →
    Γ ⊢ A type ∧ Γ ⊢ A' type →
    (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type →
    (Γ ⊢ A.refl a ∶ a ≃[A] a) ∧ (Γ ⊢ A'.refl a' ∶ a ≃[A] a) ∧ Γ ⊢ a ≃[A] a type :=
  by
    intro n Γ A A' a a' hAA haaA ihAA ihaaA
    repeat' apply And.intro
    · apply HasType.iden_intro
      · apply And.left ihAA
      · apply And.left ihaaA
    · apply HasType.ty_conv
      · apply HasType.iden_intro
        · apply And.right ihAA
        · apply HasType.ty_conv
          · apply And.left (And.right ihaaA)
          · apply hAA
      · apply IsEqualType.iden_form_eq
        · apply IsEqualType.type_symm
          apply hAA
        · apply IsEqualTerm.term_symm
          apply IsEqualTerm.ty_conv_eq
          · apply haaA
          · apply hAA
        · apply IsEqualTerm.term_symm haaA
    · apply IsType.iden_form
      · apply And.left ihAA
      · apply And.left ihaaA
      · apply And.left ihaaA

theorem boundary_iden_elim_eq :
  ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' a₁ a₃ A' a₂ a₄ p p' : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type →
    (Γ ⊢ b ≡ b' ∶ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉) →
      Γ ⊢ A ≡ A' type →
        (Γ ⊢ a₁ ≡ a₂ ∶ A) →
          (Γ ⊢ a₃ ≡ a₄ ∶ A') →
            (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃) →
              Γ ⊢ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉ ≡ B'⌈(ₛidₚ), a₂, a₂, A'.refl a₂⌉ type →
                Γ ⊢ B⌈(ₛidₚ), a₁, a₃, p⌉ ≡ B'⌈(ₛidₚ), a₂, a₄, p'⌉ type →
                  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type ∧
                      (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B' type →
                    (Γ ⊢ b ∶ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉) ∧
                        (Γ ⊢ b' ∶ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉) ∧ Γ ⊢ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉ type →
                      Γ ⊢ A type ∧ Γ ⊢ A' type →
                        (Γ ⊢ a₁ ∶ A) ∧ (Γ ⊢ a₂ ∶ A) ∧ Γ ⊢ A type →
                          (Γ ⊢ a₃ ∶ A') ∧ (Γ ⊢ a₄ ∶ A') ∧ Γ ⊢ A' type →
                            (Γ ⊢ p ∶ a₁ ≃[A] a₃) ∧ (Γ ⊢ p' ∶ a₁ ≃[A] a₃) ∧ Γ ⊢ a₁ ≃[A] a₃ type →
                              Γ ⊢ B⌈(ₛidₚ), a₁, a₁, A.refl a₁⌉ type ∧ Γ ⊢ B'⌈(ₛidₚ), a₂, a₂, A'.refl a₂⌉ type →
                                Γ ⊢ B⌈(ₛidₚ), a₁, a₃, p⌉ type ∧ Γ ⊢ B'⌈(ₛidₚ), a₂, a₄, p'⌉ type →
                                  (Γ ⊢ A.j B b a₁ a₃ p ∶ B⌈(ₛidₚ), a₁, a₃, p⌉) ∧
                                    (Γ ⊢ A'.j B' b' a₂ a₄ p' ∶ B⌈(ₛidₚ), a₁, a₃, p⌉) ∧ Γ ⊢ B⌈(ₛidₚ), a₁, a₃, p⌉ type
 :=
  by
    intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hAA haaA haaA' hppId hBBa hBBc ihBB ihbbB ihAA ihaaA ihaaA' ihppId ihBBa ihBBc
    repeat' apply And.intro
    · apply HasType.iden_elim
      · apply And.left ihBB
      · apply And.left ihbbB
      · apply And.left ihaaA
      · apply HasType.ty_conv
        · apply And.left ihaaA'
        · apply IsEqualType.type_symm hAA
      · apply And.left ihppId
      · apply And.left ihBBa
      · apply And.left ihBBc
    · apply HasType.ty_conv
      · apply HasType.iden_elim
        · rw [context_to_gen_ctx]
          rw [←middle_expand_context]
          apply And.left (And.right context_conversion)
          rotate_left
          · apply hAA
          · apply And.left ihAA
          · apply And.right ihAA
          · rw [middle_expand_context]
            apply And.left (And.right context_conversion)
            rotate_left
            · apply weakening_type_eq
              · apply hAA
              · apply And.left ihAA
            · apply weakening_type
              · apply And.left ihAA
              · apply And.left ihAA
            · apply weakening_type
              · apply And.right ihAA
              · apply And.left ihAA
            · simp [expand_ctx]
              apply context_conversion_type
              · apply IsType.iden_form
                · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                  apply weakening_type
                  · apply weakening_type
                    · apply And.right ihAA
                    · apply And.left ihAA
                  · apply weakening_type
                    · apply And.left ihAA
                    · apply And.left ihAA
                · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                  rw [weakening_shift_vone]
                  apply HasType.weak
                  · apply context_conversion_term
                    · apply And.left ihAA
                    · apply IsEqualType.type_symm hAA
                    · apply HasType.var
                      apply And.right ihAA
                  · apply weakening_type
                    · apply And.left ihAA
                    · apply And.left ihAA
                · apply context_conversion_term
                  · apply weakening_type
                    · apply And.left ihAA
                    · apply And.left ihAA
                  · apply weakening_type_eq
                    · apply IsEqualType.type_symm hAA
                    · apply And.left ihAA
                  · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                    apply HasType.var
                    apply context_conversion_type
                    · apply And.left ihAA
                    · apply IsEqualType.type_symm hAA
                    · apply weakening_type
                      · apply And.right ihAA
                      · apply And.right ihAA
              · apply IsEqualType.iden_form_eq
                rotate_right
                rotate_right
                rotate_right
                · apply A⌊↑ₚ↑ₚidₚ⌋
                · apply v(1)
                · apply v(0)
                · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                  rw (config := {occs := .pos [4]}) [←weakening_shift_id]
                  apply weakening_type_eq
                  · apply weakening_type_eq
                    · apply hAA
                    · apply And.left ihAA
                  · apply weakening_type
                    · apply And.left ihAA
                    · apply And.left ihAA
                · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                  simp [weakening_shift_vone]
                  apply IsEqualTerm.weak_eq
                  · apply IsEqualTerm.var_eq
                    apply And.left ihAA
                  · apply weakening_type
                    · apply And.left ihAA
                    · apply And.left ihAA
                · apply IsEqualTerm.ty_conv_eq
                  · apply IsEqualTerm.var_eq
                    apply weakening_type
                    · apply And.left ihAA
                    · apply And.left ihAA
                  · rw (config := {occs := .pos [4]}) [←weakening_shift_id]
                    apply weakening_type_eq
                    · apply weakening_type_eq
                      · apply hAA
                      · apply And.left ihAA
                    · apply weakening_type
                      · apply And.left ihAA
                      · apply And.left ihAA
              · apply And.right ihBB
        · apply HasType.ty_conv
          · apply And.left (And.right ihbbB)
          · apply hBBa
        · apply HasType.ty_conv
          · apply And.left (And.right ihaaA)
          · apply hAA
        · apply And.left (And.right ihaaA')
        · apply HasType.ty_conv
          · apply And.left (And.right ihppId)
          · apply IsEqualType.iden_form_eq
            · apply hAA
            · apply haaA
            · apply haaA'
        · apply And.right ihBBa
        · apply And.right ihBBc
      · apply IsEqualType.type_symm
        apply hBBc
    · apply And.left ihBBc

theorem boundary_univ_unit_eq :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → (Γ ⊢ 𝟙 ∶ 𝒰) ∧ (Γ ⊢ 𝟙 ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · apply HasType.univ_unit hiC
    · apply HasType.univ_unit hiC
    · apply IsType.univ_form hiC

theorem boundary_univ_empty_eq :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → (Γ ⊢ 𝟘 ∶ 𝒰) ∧ (Γ ⊢ 𝟘 ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · apply HasType.univ_empty hiC
    · apply HasType.univ_empty hiC
    · apply IsType.univ_form hiC

theorem boundary_univ_pi_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
    (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
    (Γ ⊢ A ∶ 𝒰) ∧ (Γ ⊢ A' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type →
    (Γ ⬝ A ⊢ B ∶ 𝒰) ∧ (Γ ⬝ A ⊢ B' ∶ 𝒰) ∧ Γ ⬝ A ⊢ 𝒰 type → (Γ ⊢ ΠA;B ∶ 𝒰) ∧ (Γ ⊢ ΠA';B' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ A A' B B' hAAU hBBU ihAAU ihBBU
    repeat' apply And.intro
    · apply HasType.univ_pi
      · apply And.left ihAAU
      · apply And.left ihBBU
    · apply HasType.univ_pi
      · apply And.left (And.right ihAAU)
      · apply context_conversion_term
        · apply IsType.univ_elim (And.left (And.right ihAAU))
        · apply IsEqualType.univ_elim_eq hAAU
        · apply And.left (And.right ihBBU)
    · apply IsType.univ_form (boundary_ctx_term_eq hAAU)


theorem boundary_univ_sigma_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰) →
        (Γ ⊢ A ∶ 𝒰) ∧ (Γ ⊢ A' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type →
          (Γ ⬝ A ⊢ B ∶ 𝒰) ∧ (Γ ⬝ A ⊢ B' ∶ 𝒰) ∧ Γ ⬝ A ⊢ 𝒰 type → (Γ ⊢ ΣA;B ∶ 𝒰) ∧ (Γ ⊢ ΣA';B' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ A A' B B' hAAU hBBU ihAAU ihBBU
    repeat' apply And.intro
    · apply HasType.univ_sigma
      · apply And.left ihAAU
      · apply And.left ihBBU
    · apply HasType.univ_sigma
      · apply And.left (And.right ihAAU)
      · apply context_conversion_term
        · apply IsType.univ_elim (And.left (And.right ihAAU))
        · apply IsEqualType.univ_elim_eq hAAU
        · apply And.left (And.right ihBBU)
    · apply IsType.univ_form (boundary_ctx_term_eq hAAU)

theorem boundary_univ_iden_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰) →
      (Γ ⊢ a₁ ≡ a₂ ∶ A) →
        (Γ ⊢ a₃ ≡ a₄ ∶ A) →
          (Γ ⊢ A ∶ 𝒰) ∧ (Γ ⊢ A' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type →
            (Γ ⊢ a₁ ∶ A) ∧ (Γ ⊢ a₂ ∶ A) ∧ Γ ⊢ A type →
              (Γ ⊢ a₃ ∶ A) ∧ (Γ ⊢ a₄ ∶ A) ∧ Γ ⊢ A type → (Γ ⊢ a₁ ≃[A] a₃ ∶ 𝒰) ∧ (Γ ⊢ a₂ ≃[A'] a₄ ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ A A' a₁ a₂ a₃ a₄ hAAU haaA haaA' ihAAU ihaaA ihaaA'
    repeat' apply And.intro
    · apply HasType.univ_iden
      · apply And.left ihAAU
      · apply And.left ihaaA
      · apply And.left ihaaA'
    · apply HasType.univ_iden
      · apply And.left (And.right ihAAU)
      · apply HasType.ty_conv
        · apply And.left (And.right ihaaA)
        · apply IsEqualType.univ_elim_eq hAAU
      · apply HasType.ty_conv
        · apply And.left (And.right ihaaA')
        · apply IsEqualType.univ_elim_eq hAAU
    · apply And.right (And.right ihAAU)

theorem boundary_ty_conv_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a b A B : Tm n},
    (Γ ⊢ a ≡ b ∶ A) →
      Γ ⊢ A ≡ B type →
        (Γ ⊢ a ∶ A) ∧ (Γ ⊢ b ∶ A) ∧ Γ ⊢ A type → Γ ⊢ A type ∧ Γ ⊢ B type → (Γ ⊢ a ∶ B) ∧ (Γ ⊢ b ∶ B) ∧ Γ ⊢ B type :=
  by
    intro n Γ a b A B habA hAB ihabA ihAB
    repeat' apply And.intro
    · apply HasType.ty_conv
      · apply And.left ihabA
      · apply hAB
    · apply HasType.ty_conv
      · apply And.left (And.right ihabA)
      · apply hAB
    · apply And.right ihAB

theorem boundary_term_symm :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A : Tm n},
    (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type → (Γ ⊢ a' ∶ A) ∧ (Γ ⊢ a ∶ A) ∧ Γ ⊢ A type :=
  by
    intro n Γ a a' A haaA ihaaA
    repeat' apply And.intro
    · apply And.left (And.right ihaaA)
    · apply And.left ihaaA
    · apply And.right (And.right ihaaA)

theorem boundary_term_trans :
    ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
    (Γ ⊢ a ≡ b ∶ T) →
      (Γ ⊢ b ≡ c ∶ T) →
        (Γ ⊢ a ∶ T) ∧ (Γ ⊢ b ∶ T) ∧ Γ ⊢ T type →
          (Γ ⊢ b ∶ T) ∧ (Γ ⊢ c ∶ T) ∧ Γ ⊢ T type → (Γ ⊢ a ∶ T) ∧ (Γ ⊢ c ∶ T) ∧ Γ ⊢ T type :=
  by
    intro n Γ T a b c habT hbcT ihabT ihbcT
    repeat' apply And.intro
    · apply And.left ihabT
    · apply And.left (And.right ihbcT)
    · apply And.right (And.right ihabT)
