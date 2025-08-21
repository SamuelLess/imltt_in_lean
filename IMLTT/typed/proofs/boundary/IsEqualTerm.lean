import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.WeakSubstitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.FunctionalityTyping
import IMLTT.typed.proofs.admissable.ContextConversion

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.boundary.Helpers

theorem boundary_var_eq :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type
    → Γ ⊢ A type
    → (Γ ⬝ A ⊢ v(0) ∶ A⌊↑ₚidₚ⌋) ∧ (Γ ⬝ A ⊢ v(0) ∶ A⌊↑ₚidₚ⌋) ∧ Γ ⬝ A ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n Γ A hA ihA
    apply And.intro
    · apply HasType.var hA
    · apply And.intro
      · apply HasType.var hA
      · apply weakening_type hA hA

theorem boundary_weak_eq :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ≡ v(i) ∶ A)
    → Γ ⊢ B type
    → (Γ ⊢ v(i) ∶ A) ∧ (Γ ⊢ v(i) ∶ A) ∧ Γ ⊢ A type
    → Γ ⊢ B type
    → (Γ ⬝ B ⊢ v(i)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋) ∧ (Γ ⬝ B ⊢ v(i)⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋) ∧ Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ type :=
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
    Γ ⬝ 𝟙 ⊢ A type
    → (Γ ⊢ a ∶ A⌈⋆⌉₀)
    → Γ ⬝ 𝟙 ⊢ A type
    → Γ ⊢ A⌈⋆⌉₀ type
    → (Γ ⊢ A.indUnit ⋆ a ∶ A⌈⋆⌉₀) ∧ (Γ ⊢ a ∶ A⌈⋆⌉₀) ∧ Γ ⊢ A⌈⋆⌉₀ type :=
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
    (Γ ⬝ A ⊢ b ∶ B)
    → (Γ ⊢ a ∶ A)
    → Γ ⬝ A ⊢ B type
    → Γ ⊢ A type
    → (Γ ⊢ (λA; b)◃a ∶ B⌈a⌉₀) ∧ (Γ ⊢ b⌈a⌉₀ ∶ B⌈a⌉₀) ∧ Γ ⊢ B⌈a⌉₀ type :=
  by
    intro n Γ A b B a hbB haA ihbB ihaA
    repeat' apply And.intro
    · apply HasType.pi_elim
      · apply HasType.pi_intro
        apply hbB
      · apply haA
    · apply substitution_term
      · apply hbB
      · apply haA
    · apply substitution_type
      · apply ihbB
      · apply haA

theorem boundary_sigma_comp :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
  (Γ ⬝ ΣA;B) ⊢ C type →
    (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉) →
      (Γ ⊢ a ∶ A) →
        (Γ ⊢ b ∶ B⌈a⌉₀) →
          (Γ ⬝ ΣA;B) ⊢ C type →
            Γ ⬝ A ⬝ B ⊢ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ type →
              Γ ⊢ A type →
                Γ ⊢ B⌈a⌉₀ type →
                  (Γ ⊢ A.indSigma B C c (a&b) ∶ C⌈a&b⌉₀) ∧ (Γ ⊢ c⌈(ₛidₚ)⋄ a⋄ b⌉ ∶ C⌈a&b⌉₀) ∧ Γ ⊢ C⌈a&b⌉₀ type :=
  by
    intro n Γ a A b B C c hC hcC haA hbB ihC ihcC ihaA ihbB
    repeat' apply And.intro
    · apply HasType.sigma_elim
      · apply hC
      · apply hcC
      · apply HasType.sigma_intro
        · apply haA
        · apply hbB
        · apply ctx_extr (boundary_ctx_term hcC)
    · rw [context_to_gen_ctx] at hcC
      have h1 := substitution_general_term hcC haA
      simp only [substitute_into_gen_ctx] at h1
      simp only [n_substitution_zero] at h1
      simp only [zero_substitution] at h1
      simp only [substitution_conv_zero] at h1
      have h2 := substitution_term h1 hbB
      apply_subst_eq h2
    · apply substitution_type
      · apply hC
      · apply HasType.sigma_intro
        · apply haA
        · apply hbB
        · apply ctx_extr (boundary_ctx_term hcC)

theorem boundary_nat_zero_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ 𝓏 ∶ 𝒩)
    → Γ ⬝ 𝒩 ⊢ A type
    → Γ ⊢ A⌈𝓏⌉₀ type
    → Γ ⬝ 𝒩 ⬝ A ⊢ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ type
    → Γ ⊢ 𝒩 type
    → (Γ ⊢ A.indNat z s 𝓏 ∶ A⌈𝓏⌉₀) ∧ (Γ ⊢ z ∶ A⌈𝓏⌉₀) ∧ Γ ⊢ A⌈𝓏⌉₀ type :=
  by
    intro n Γ z A s hA hzA hsA hzNat ihA ihzA ihsA ihzNat
    repeat' apply And.intro
    · apply HasType.nat_elim
      · apply hA
      · apply hzA
      · apply hsA
      · apply hzNat
    · apply hzA
    · apply substitution_type
      · apply hA
      · apply hzNat

theorem boundary_nat_succ_comp :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ∶ 𝒩)
    → Γ ⬝ 𝒩 ⊢ A type
    → Γ ⊢ A⌈𝓏⌉₀ type
    → Γ ⬝ 𝒩 ⬝ A ⊢ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ type
    → Γ ⊢ 𝒩 type
    → (Γ ⊢ A.indNat z s 𝓈(x) ∶ A⌈𝓈(x)⌉₀)
      ∧ (Γ ⊢ s⌈(ₛidₚ)⋄ x⋄ A.indNat z s x⌉ ∶ A⌈𝓈(x)⌉₀)
      ∧ Γ ⊢ A⌈𝓈(x)⌉₀ type :=
  by
    intro n Γ z x A s hA hzA hsA hsNat ihA ihzA ihsA ihsNat
    repeat' apply And.intro
    · apply HasType.nat_elim
      · apply hA
      · apply hzA
      · apply hsA
      · apply HasType.nat_succ_intro hsNat
    · rw [←substitution_separate]
      simp only [substitution_conv_zero]
      rw [←substitution_shift_substitute_zero (A := A⌈𝓈(x)⌉₀)]
      apply substitution_term
      · rw [context_to_gen_ctx] at hsA
        apply_subst_eq substitution_general_term hsA hsNat
      · apply_subst_eq HasType.nat_elim hA hzA hsA hsNat
    · apply substitution_type
      · apply hA
      · apply HasType.nat_succ_intro hsNat

theorem boundary_iden_comp :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
    → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → (Γ ⊢ a ∶ A)
    → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
    → Γ ⬝ A ⊢ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ type
    → Γ ⊢ A type
    → (Γ ⊢ A.j B b a a (A.refl a) ∶ B⌈(ₛidₚ)⋄ a⋄ a⋄ A.refl a⌉)
      ∧ (Γ ⊢ b⌈a⌉₀ ∶ B⌈(ₛidₚ)⋄ a⋄ a⋄ A.refl a⌉)
      ∧ Γ ⊢ B⌈(ₛidₚ)⋄ a⋄ a⋄ A.refl a⌉ type
 :=
  by
    intro n Γ A B b a hB hbB haA ihB ihbB ihaA
    repeat' apply And.intro
    · apply HasType.iden_elim
      · apply hB
      · apply hbB
      · apply haA
      · apply haA
      · apply HasType.iden_intro
        · apply ihaA
        · apply haA
    · apply_subst_eq substitution_term hbB haA
    · apply_subst_eq substitution_type ihbB haA

theorem boundary_unit_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx
    → Γ ctx
    → (Γ ⊢ ⋆ ∶ 𝟙) ∧ (Γ ⊢ ⋆ ∶ 𝟙) ∧ Γ ⊢ 𝟙 type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · apply HasType.unit_intro hiC
    · apply HasType.unit_intro hiC
    · apply IsType.unit_form hiC

theorem boundary_unit_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {a a' b b' : Tm n},
    Γ ⬝ 𝟙 ⊢ A ≡ A' type
    → (Γ ⊢ a ≡ a' ∶ A⌈⋆⌉₀)
    → (Γ ⊢ b ≡ b' ∶ 𝟙)
    → Γ ⬝ 𝟙 ⊢ A type ∧ Γ ⬝ 𝟙 ⊢ A' type
    → (Γ ⊢ a ∶ A⌈⋆⌉₀) ∧ (Γ ⊢ a' ∶ A⌈⋆⌉₀) ∧ Γ ⊢ A⌈⋆⌉₀ type
    → (Γ ⊢ b ∶ 𝟙) ∧ (Γ ⊢ b' ∶ 𝟙) ∧ Γ ⊢ 𝟙 type
    → (Γ ⊢ A.indUnit b a ∶ A⌈b⌉₀) ∧ (Γ ⊢ A'.indUnit b' a' ∶ A⌈b⌉₀) ∧ Γ ⊢ A⌈b⌉₀ type :=
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
            · apply hAA
            · apply HasType.unit_intro (boundary_ctx_term_eq haaA)
        · apply And.left (And.right ihbb1)
      · have hAA' := substitution_type_eq (hAA) (And.left (And.right ihbb1))
        apply IsEqualType.type_trans
        · apply IsEqualType.type_symm hAA'
        · apply functionality_typing_type
          · apply And.left ihAA
          · apply IsEqualTerm.term_symm hbb1
          · apply And.left (And.right ihbb1)
          · apply And.left ihbb1
    · apply substitution_type
      · apply And.left ihAA
      · apply And.left ihbb1

theorem boundary_empty_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm (n + 1)} {b b' : Tm n},
    Γ ⬝ 𝟘 ⊢ A ≡ A' type
    → (Γ ⊢ b ≡ b' ∶ 𝟘)
    → Γ ⬝ 𝟘 ⊢ A type ∧ Γ ⬝ 𝟘 ⊢ A' type
    → (Γ ⊢ b ∶ 𝟘) ∧ (Γ ⊢ b' ∶ 𝟘) ∧ Γ ⊢ 𝟘 type
    → (Γ ⊢ A.indEmpty b ∶ A⌈b⌉₀) ∧ (Γ ⊢ A'.indEmpty b' ∶ A⌈b⌉₀) ∧ Γ ⊢ A⌈b⌉₀ type :=
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
      · have hAA' := substitution_type_eq (hAA) (And.left (And.right ihbb0))
        apply IsEqualType.type_trans
        · apply IsEqualType.type_symm hAA'
        · apply functionality_typing_type
          · apply And.left ihAA
          · apply IsEqualTerm.term_symm hbb0
          · apply And.left (And.right ihbb0)
          · apply And.left ihbb0
    · apply substitution_type
      · apply And.left ihAA
      · apply And.left ihbb0

theorem boundary_pi_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {b b' B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ≡ b' ∶ B)
    → Γ ⊢ A ≡ A' type
    → (Γ ⬝ A ⊢ b ∶ B) ∧ (Γ ⬝ A ⊢ b' ∶ B) ∧ Γ ⬝ A ⊢ B type
    → Γ ⊢ A type ∧ Γ ⊢ A' type
    → (Γ ⊢ λA; b ∶ ΠA;B) ∧ (Γ ⊢ λA'; b' ∶ ΠA;B) ∧ Γ ⊢ ΠA;B type :=
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
    (Γ ⊢ f ≡ f' ∶ ΠA;B)
    → (Γ ⊢ a ≡ a' ∶ A)
    → (Γ ⊢ f ∶ ΠA;B) ∧ (Γ ⊢ f' ∶ ΠA;B) ∧ Γ ⊢ ΠA;B type
    → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type
    → (Γ ⊢ f◃a ∶ B⌈a⌉₀) ∧ (Γ ⊢ f'◃a' ∶ B⌈a⌉₀) ∧ Γ ⊢ B⌈a⌉₀ type :=
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
      · have hPiInv := pi_is_type_inversion (And.right (And.right ihffPi))
        apply And.right hPiInv
      · apply And.left ihaaA

theorem boundary_sigma_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a a' A b b' : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ≡ a' ∶ A)
    → (Γ ⊢ b ≡ b' ∶ B⌈a⌉₀)
    → Γ ⬝ A ⊢ B type
    → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type
    → (Γ ⊢ b ∶ B⌈a⌉₀) ∧ (Γ ⊢ b' ∶ B⌈a⌉₀) ∧ Γ ⊢ B⌈a⌉₀ type
    → Γ ⬝ A ⊢ B type
    → (Γ ⊢ a&b ∶ ΣA;B) ∧ (Γ ⊢ a'&b' ∶ ΣA;B) ∧ Γ ⊢ ΣA;B type :=
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

theorem boundary_sigma_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {A' : Tm n} {B' : Tm (n + 1)} {p p' : Tm n} {C C' : Tm (n + 1)}
      {c c' : Tm (n + 1 + 1)},
    (Γ ⬝ ΣA;B) ⊢ C ≡ C' type
    → (Γ ⬝ A ⬝ B ⊢ c ≡ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
    → Γ ⊢ A ≡ A' type
    → Γ ⬝ A ⊢ B ≡ B' type
    → (Γ ⊢ p ≡ p' ∶ ΣA;B)
    → (Γ ⬝ ΣA;B) ⊢ C type ∧ (Γ ⬝ ΣA;B) ⊢ C' type
    → (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
      ∧ (Γ ⬝ A ⬝ B ⊢ c' ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉) ∧ Γ ⬝ A ⬝ B ⊢ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ type
    → Γ ⊢ A type ∧ Γ ⊢ A' type
    → Γ ⬝ A ⊢ B type ∧ Γ ⬝ A ⊢ B' type
    → (Γ ⊢ p ∶ ΣA;B) ∧ (Γ ⊢ p' ∶ ΣA;B) ∧ Γ ⊢ ΣA;B type
    → (Γ ⊢ A.indSigma B C c p ∶ C⌈p⌉₀) ∧ (Γ ⊢ A'.indSigma B' C' c' p' ∶ C⌈p⌉₀) ∧ Γ ⊢ C⌈p⌉₀ type :=
  by
    intro n Γ A B A' B' p p' C C' c c' hCC hccC hAA hBB hppSi ihCC ihccC ihAA ihBB ihppSi
    repeat' apply And.intro
    · apply HasType.sigma_elim
      · apply And.left ihCC
      · apply And.left ihccC
      · apply And.left ihppSi
    · apply HasType.ty_conv
      · apply HasType.sigma_elim
        · apply context_conversion_type
          · apply IsType.sigma_form
            · apply And.right ihAA
            · apply context_conversion_type
              · apply And.right ihAA
              · apply hAA
              · apply And.right ihBB
          · apply IsEqualType.sigma_form_eq hAA hBB
          · apply And.right ihCC
        · rw [←empty_expand_context (Γ := Γ)]
          rw [extend_expand_context]
          rw [extend_expand_context]
          rw [middle_expand_context]
          apply context_conversion_general_term
          rotate_left
          · apply hAA
          · apply And.left ihAA
          · apply And.right ihAA
          · simp [expand_ctx]
            apply context_conversion_term
            · apply And.right ihBB
            · apply hBB
            · apply HasType.ty_conv
              · apply And.left (And.right ihccC)
              · have h1 := weakening_second_type_eq hCC (And.left ihAA)
                have h2 := weakening_second_type_eq h1 (And.left ihBB)
                have ht : Γ ⬝ A ⬝ B ⊢ v(1)&v(0) ∶ (ΣA;B)⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋ :=
                  by
                    apply HasType.sigma_intro
                    · rw [weakening_shift_vone]
                      apply HasType.weak
                      · apply HasType.var
                        apply And.left ihAA
                      · apply And.left ihBB
                    · have h3 := HasType.var (And.left ihBB)
                      apply_subst_eq HasType.var (And.left ihBB)
                    · apply weakening_second_type
                      · apply weakening_second_type
                        · apply And.left ihBB
                        · apply And.left ihAA
                      · apply And.left ihBB
                apply_subst_eq substitution_type_eq h2 ht
        · apply HasType.ty_conv
          · apply And.left (And.right ihppSi)
          · apply IsEqualType.sigma_form_eq hAA hBB
      · apply IsEqualType.type_symm
        apply IsEqualType.type_trans
        · apply functionality_typing_type
          · apply And.left ihCC
          · apply hppSi
          · apply And.left ihppSi
          · apply And.left (And.right ihppSi)
        · apply substitution_type_eq
          · apply hCC
          · apply And.left (And.right ihppSi)
    · apply substitution_type
      · apply And.left ihCC
      · apply And.left ihppSi

theorem boundary_nat_zero_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → (Γ ⊢ 𝓏 ∶ 𝒩) ∧ (Γ ⊢ 𝓏 ∶ 𝒩) ∧ Γ ⊢ 𝒩 type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · apply HasType.nat_zero_intro hiC
    · apply HasType.nat_zero_intro hiC
    · apply IsType.nat_form hiC

theorem boundary_nat_succ_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {x x' : Tm n},
    (Γ ⊢ x ≡ x' ∶ 𝒩)
    → (Γ ⊢ x ∶ 𝒩) ∧ (Γ ⊢ x' ∶ 𝒩) ∧ Γ ⊢ 𝒩 type
    → (Γ ⊢ 𝓈(x) ∶ 𝒩) ∧ (Γ ⊢ 𝓈(x') ∶ 𝒩) ∧ Γ ⊢ 𝒩 type :=
  by
    intro n Γ x x' hxxNat ihxxNat
    repeat' apply And.intro
    · apply HasType.nat_succ_intro
      apply And.left ihxxNat
    · apply HasType.nat_succ_intro
      apply And.left (And.right ihxxNat)
    · apply And.right (And.right ihxxNat)

theorem boundary_nat_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {z z' x x' : Tm n} {A A' : Tm (n + 1)} {s s' : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A ≡ A' type
    → (Γ ⊢ z ≡ z' ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ≡ s' ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ≡ x' ∶ 𝒩)
    → Γ ⬝ 𝒩 ⊢ A type ∧ Γ ⬝ 𝒩 ⊢ A' type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀) ∧ (Γ ⊢ z' ∶ A⌈𝓏⌉₀) ∧ Γ ⊢ A⌈𝓏⌉₀ type
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋) ∧ (Γ ⬝ 𝒩 ⬝ A ⊢ s' ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
      ∧ Γ ⬝ 𝒩 ⬝ A ⊢ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ type
    → (Γ ⊢ x ∶ 𝒩) ∧ (Γ ⊢ x' ∶ 𝒩) ∧ Γ ⊢ 𝒩 type
    → (Γ ⊢ A.indNat z s x ∶ A⌈x⌉₀) ∧ (Γ ⊢ A'.indNat z' s' x' ∶ A⌈x⌉₀) ∧ Γ ⊢ A⌈x⌉₀ type :=
  by
    intro n Γ z z' x x' A A' s s' hAA hzzA hssA hxxNat ihAA ihzzA ihssA ihxxNat
    repeat' apply And.intro
    · apply HasType.nat_elim
      · apply And.left ihAA
      · apply And.left ihzzA
      · apply And.left ihssA
      · apply And.left ihxxNat
    · apply HasType.ty_conv
      · apply HasType.nat_elim
        · apply And.right ihAA
        · apply HasType.ty_conv
          · apply And.left (And.right ihzzA)
          · apply substitution_type_eq
            · apply hAA
            · apply HasType.nat_zero_intro
              apply boundary_ctx_term_eq hzzA
        · apply context_conversion_term
          · apply And.right ihAA
          · apply hAA
          · apply HasType.ty_conv
            · apply And.left (And.right ihssA)
            · have hVar := HasType.nat_succ_intro (HasType.var (ctx_extr (boundary_ctx_type_eq hAA)))
              apply weakening_type_eq
              · rw [←empty_expand_context (Γ := Γ ⬝ 𝒩 )]
                rw [←n_substitution_shift_zero]
                rw [←empty_extend_expand_context_n_substitution_shift]
                apply weak_substitution_general_type_eq
                · apply hAA
                · rw (config := {occs := .pos [2]}) [←weakening_nat] at hVar
                  apply hVar
              · apply And.left ihAA
        · apply And.left (And.right ihxxNat)
      · apply IsEqualType.type_symm
        apply IsEqualType.type_trans
        rotate_right
        · apply A'⌈x⌉₀
        · apply substitution_type_eq
          · apply hAA
          · apply And.left ihxxNat
        · apply functionality_typing_type
          · apply And.right ihAA
          · apply hxxNat
          · apply And.left ihxxNat
          · apply And.left (And.right ihxxNat)
    · apply substitution_type
      · apply And.left ihAA
      · apply And.left ihxxNat

theorem boundary_iden_intro_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a a' : Tm n},
    Γ ⊢ A ≡ A' type
    → (Γ ⊢ a ≡ a' ∶ A)
    → Γ ⊢ A type ∧ Γ ⊢ A' type
    → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type
    → (Γ ⊢ A.refl a ∶ a ≃[A] a) ∧ (Γ ⊢ A'.refl a' ∶ a ≃[A] a) ∧ Γ ⊢ a ≃[A] a type :=
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

set_option maxHeartbeats 3000000
theorem boundary_iden_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B B' : Tm (n + 1 + 1 + 1)} {b b' : Tm (n + 1)} {a₁ a₃ A' a₂ a₄ p p' : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B ≡ B' type
    → (Γ ⬝ A ⊢ b ≡ b' ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → Γ ⊢ A ≡ A' type
    → (Γ ⊢ a₁ ≡ a₂ ∶ A)
    → (Γ ⊢ a₃ ≡ a₄ ∶ A')
    → (Γ ⊢ p ≡ p' ∶ a₁ ≃[A] a₃)
    → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
      ∧ (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B' type
    → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
      ∧ (Γ ⬝ A ⊢ b' ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
      ∧ Γ ⬝ A ⊢ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ type
    → Γ ⊢ A type ∧ Γ ⊢ A' type
    → (Γ ⊢ a₁ ∶ A) ∧ (Γ ⊢ a₂ ∶ A) ∧ Γ ⊢ A type
    → (Γ ⊢ a₃ ∶ A') ∧ (Γ ⊢ a₄ ∶ A') ∧ Γ ⊢ A' type
    → (Γ ⊢ p ∶ a₁ ≃[A] a₃) ∧ (Γ ⊢ p' ∶ a₁ ≃[A] a₃) ∧ Γ ⊢ a₁ ≃[A] a₃ type
    → (Γ ⊢ A.j B b a₁ a₃ p ∶ B⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉)
      ∧ (Γ ⊢ A'.j B' b' a₂ a₄ p' ∶ B⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉)
      ∧ Γ ⊢ B⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉ type
 :=
  by
    intro n Γ A B B' b b' a₁ a₃ A' a₂ a₄ p p' hBB hbbB hAA haaA haaA' hppId ihBB ihbbB ihAA ihaaA ihaaA' ihppId
    have h1 := weakening_type ihAA.left ihAA.left
    have h2 := weakening_type ihAA.right ihAA.right
    have h3 := weakening_type ihAA.right ihAA.left
    have h4 := weakening_type_eq hAA ihAA.left
    have h5 := HasType.weak (HasType.var (And.left ihAA)) h1
    have h6 := weakening_type h1 h1
    have h7 := HasType.weak (HasType.var (And.left ihAA)) h1
    have h8 := weakening_type h3 h1
    have h9 : Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⊢ A'⌊↑ₚ↑ₚidₚ⌋ ≡ A⌊↑ₚ↑ₚidₚ⌋ type :=
      by
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        rw (config := {occs := .pos [4]}) [←weakening_shift_id]
        apply IsEqualType.type_symm
        apply weakening_type_eq h4 h1
    have h10 : Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⊢ v(1) ≡ v(1) ∶ A⌊↑ₚ↑ₚidₚ⌋ :=
      by
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        rw [weakening_shift_vone]
        apply IsEqualTerm.weak_eq
        · apply IsEqualTerm.var_eq (And.left ihAA)
        · apply weakening_type (And.left ihAA) (And.left ihAA)
    repeat' apply And.intro
    · apply HasType.iden_elim
      · apply And.left ihBB
      · apply And.left ihbbB
      · apply And.left ihaaA
      · apply HasType.ty_conv
        · apply And.left ihaaA'
        · apply IsEqualType.type_symm hAA
      · apply And.left ihppId
    · apply HasType.ty_conv
      · apply HasType.iden_elim
        · rw [context_to_gen_ctx]
          rw [←middle_expand_context]
          apply context_conversion_general_type
          rotate_left
          · apply hAA
          · apply And.left ihAA
          · apply And.right ihAA
          · rw [middle_expand_context]
            apply context_conversion_general_type
            rotate_left
            · apply h4
            · apply h1
            · apply h3
            · simp [expand_ctx]
              apply context_conversion_type
              · apply IsType.iden_form
                · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                  apply h8
                · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                  rw [weakening_shift_vone]
                  apply HasType.weak
                  · apply context_conversion_term
                    · apply And.left ihAA
                    · apply IsEqualType.type_symm hAA
                    · apply HasType.var
                      apply And.right ihAA
                  · apply h1
                · apply context_conversion_term
                  · apply h1
                  · apply weakening_type_eq
                    · apply IsEqualType.type_symm hAA
                    · apply And.left ihAA
                  · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                    apply HasType.var
                    apply context_conversion_type
                    · apply And.left ihAA
                    · apply IsEqualType.type_symm hAA
                    · apply h2
              · apply IsEqualType.iden_form_eq
                rotate_right
                rotate_right
                rotate_right
                · apply A⌊↑ₚ↑ₚidₚ⌋
                · apply v(1)
                · apply v(0)
                · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                  rw (config := {occs := .pos [4]}) [←weakening_shift_id]
                  apply weakening_type_eq h4 h1
                · apply_subst_eq IsEqualTerm.weak_eq (IsEqualTerm.var_eq ihAA.left) h1
                · apply IsEqualTerm.ty_conv_eq
                  · apply IsEqualTerm.var_eq h1
                  · rw (config := {occs := .pos [4]}) [←weakening_shift_id]
                    apply weakening_type_eq h4 h1
              · apply And.right ihBB
        · apply context_conversion_term ihAA.right hAA
          apply HasType.ty_conv
          · apply And.left (And.right ihbbB)
          · rw [context_to_gen_ctx] at hBB
            have hrefl : Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⊢ (.refl (A⌊↑ₚ↑ₚidₚ⌋) v(1)) ∶ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(1) :=
              by apply HasType.iden_intro
                 · apply_subst_eq h6
                 · apply_subst_eq h5
            apply IsEqualType.type_trans
            · have h := weak_substitution_general_type_eq hBB h7
              simp only [substitute_shift_into_gen_ctx] at h
              simp only [n_substitution_shift_zero] at h
              simp only [id_vone_to_vtwo] at h
              simp only [expand_ctx] at h
              apply_subst_eq substitution_type_eq (substitution_type_eq h hrefl) (HasType.var (And.left ihAA))
            · rw [context_to_gen_ctx] at ihBB
              have h := weak_substitution_general_type ihBB.right
                    (by
                      apply HasType.weak
                      · apply HasType.var (And.left ihAA)
                      · apply weakening_type (And.left ihAA) (And.left ihAA)
                    )
              simp only [substitute_shift_into_gen_ctx] at h
              simp only [n_substitution_shift_zero] at h
              simp only [id_vone_to_vtwo] at h
              simp only [expand_ctx] at h
              have hrefl' : Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⊢ (.refl (A'⌊↑ₚ↑ₚidₚ⌋) v(1)) ∶ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(1) :=
                by
                  apply HasType.ty_conv
                  · apply HasType.iden_intro
                    · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                      apply h8
                    · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
                      rw [weakening_shift_vone]
                      apply HasType.weak
                      · apply HasType.ty_conv
                        · apply HasType.var (And.left ihAA)
                        · apply h4
                      · apply h1
                  · apply IsEqualType.iden_form_eq
                    · apply h9
                    · apply IsEqualTerm.ty_conv_eq
                      · apply h10
                      · apply IsEqualType.type_symm h9
                    · apply h10
              have hrefleq : Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⊢ (.refl (A⌊↑ₚ↑ₚidₚ⌋) v(1)) ≡ (.refl (A'⌊↑ₚ↑ₚidₚ⌋) v(1)) ∶ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(1) :=
                by apply IsEqualTerm.iden_intro_eq
                   · apply IsEqualType.type_symm h9
                   · apply h10
              have hpre := functionality_typing_type h hrefleq hrefl hrefl'
              apply_subst_eq substitution_type_eq hpre (HasType.var (And.left ihAA))
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
      · apply IsEqualType.type_symm
        apply IsEqualType.type_trans
        rotate_right
        · apply B'⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉
        · rw [context_to_gen_ctx] at hBB
          rw [←middle_expand_context (Γ := Γ ⬝ A)] at hBB
          have h := substitution_general_type_eq hBB (And.left ihaaA)
          simp only [substitute_into_gen_ctx] at h
          rw [n_substitution_zero] at h
          rw [zero_substitution] at h
          rw [substitution_conv_zero] at h
          rw [substitution_shift_substitute_zero] at h
          rw [middle_expand_context] at h
          have h2 := substitution_general_type_eq h (HasType.ty_conv (And.left ihaaA') (IsEqualType.type_symm hAA))
          have h3 :=
            by
              apply substitution_type_eq
              rotate_left
              · apply (And.left ihppId)
              rotate_right
              · apply_subst_eq h2
                simp [substitute_into_gen_ctx]
                simp [expand_ctx]
                substitution_norm
          apply_subst_eq h3
        · apply IsEqualType.type_trans
          rotate_right
          · apply B'⌈(ₛidₚ)⋄ a₂⋄ a₃⋄ p⌉
          · rw [context_to_gen_ctx] at ihBB
            rw [←middle_expand_context (Γ := Γ ⬝ A)] at ihBB
            have h1 := (And.left (And.right functionality_typing))
                        haaA (And.left ihaaA) (And.left (And.right ihaaA)) (And.right ihBB)
            simp only [substitute_into_gen_ctx] at h1
            rw [n_substitution_zero] at h1
            rw [zero_substitution] at h1
            rw [substitution_conv_zero] at h1
            rw [substitution_shift_substitute_zero] at h1
            rw [middle_expand_context] at h1
            have h2 := substitution_general_type_eq
                        h1 (HasType.ty_conv (And.left ihaaA') (IsEqualType.type_symm hAA))
            have h3 :=
              by
                apply substitution_type_eq
                rotate_left
                · apply (And.left ihppId)
                rotate_right
                · apply_subst_eq h2
                  simp [substitute_into_gen_ctx]
                  simp [expand_ctx]
                  substitution_norm
            apply_subst_eq h3
          · apply IsEqualType.type_trans
            rotate_right
            · apply B'⌈(ₛidₚ)⋄ a₂⋄ a₄⋄ p⌉
            · rw [context_to_gen_ctx] at ihBB
              rw [←middle_expand_context (Γ := Γ ⬝ A)] at ihBB
              have h1 := (And.left (And.right substitution))
                          (And.right ihBB) (And.left (And.right ihaaA))
              simp only [substitute_into_gen_ctx] at h1
              rw [n_substitution_zero] at h1
              rw [zero_substitution] at h1
              rw [substitution_conv_zero] at h1
              rw [substitution_shift_substitute_zero] at h1
              rw [middle_expand_context] at h1
              have h2 := functionality_typing_general_type h1
                          (IsEqualTerm.ty_conv_eq (IsEqualTerm.term_symm haaA') (IsEqualType.type_symm hAA))
                          (HasType.ty_conv (And.left (And.right ihaaA')) (IsEqualType.type_symm hAA))
                          (HasType.ty_conv (And.left ihaaA') (IsEqualType.type_symm hAA))
              have hIdEq : Γ ⊢ a₁ ≃[A] a₃ ≡ a₂ ≃[A] a₄ type :=
                  IsEqualType.iden_form_eq (defeq_refl_type (And.left ihAA))
                      haaA (IsEqualTerm.ty_conv_eq haaA' (IsEqualType.type_symm hAA))
              have h3 :=
                by
                  apply substitution_type_eq
                  rotate_left
                  · apply (HasType.ty_conv (And.left ihppId) hIdEq)
                  rotate_right
                  · apply_subst_eq h2
                    simp [substitute_into_gen_ctx]
                    simp [expand_ctx]
                    substitution_norm
              apply IsEqualType.type_symm
              apply_subst_eq h3
            · rw [context_to_gen_ctx] at ihBB
              rw [←middle_expand_context (Γ := Γ ⬝ A)] at ihBB
              have h1 := substitution_general_type (And.right ihBB) (And.left (And.right ihaaA))
              simp only [substitute_into_gen_ctx] at h1
              rw [n_substitution_zero] at h1
              rw [zero_substitution] at h1
              rw [substitution_conv_zero] at h1
              rw [substitution_shift_substitute_zero] at h1
              rw [middle_expand_context] at h1
              have h2 := substitution_general_type
                          (h1)
                          (HasType.ty_conv (And.left (And.right ihaaA')) (IsEqualType.type_symm hAA))
              rw [substitute_into_gen_ctx] at h2
              have h2_new : Γ ⬝ (a₂ ≃[A] a₄) ⊢ B'⌈a₂/ₙ(Nat.le_succ_of_le (Nat.le_succ n))⌉⌈a₄/ₙ(Nat.le_succ n)⌉ type :=
                by
                  apply_subst_eq h2
              have hIdEq : Γ ⊢ a₁ ≃[A] a₃ ≡ a₂ ≃[A] a₄ type :=
                  IsEqualType.iden_form_eq (defeq_refl_type (And.left ihAA))
                      haaA (IsEqualTerm.ty_conv_eq haaA' (IsEqualType.type_symm hAA))
              have hnew_old : (Γ ⬝ a₁ ≃[A] a₃) ⊢ B'⌈a₂/ₙ(by omega)⌉⌈a₄/ₙ(by omega)⌉ type :=
                  context_conversion_type (And.right (And.right ihppId)) (IsEqualType.type_symm hIdEq)
                  (by apply_subst_eq h2_new)
              have h3 := functionality_typing_type
                          hnew_old
                          (IsEqualTerm.term_symm hppId)
                          (And.left (And.right ihppId))
                          (And.left ihppId)
              apply IsEqualType.type_symm
              apply_subst_eq h3
    · have ihB := And.left ihBB
      rw [context_to_gen_ctx] at ihB
      rw [←middle_expand_context (Γ := Γ ⬝ A)] at ihB
      have h := substitution_general_type (ihB) (And.left ihaaA)
      simp only [substitute_into_gen_ctx] at h
      rw [n_substitution_zero] at h
      rw [zero_substitution] at h
      rw [substitution_conv_zero] at h
      rw [substitution_shift_substitute_zero] at h
      rw [middle_expand_context] at h
      have h2 := substitution_general_type
                  h (HasType.ty_conv (And.left ihaaA') (IsEqualType.type_symm hAA))
      have h3 : Γ ⊢ B⌈a₁/ₙ(by omega)⌉⌈a₃/ₙ(by omega)⌉⌈p⌉₀ type :=
        by
          apply substitution_type
          rotate_left
          · apply (And.left ihppId)
          · apply_subst_eq h2
            simp [substitute_into_gen_ctx]
            simp [expand_ctx]
            substitution_norm
      · apply_subst_eq h3

theorem boundary_univ_unit_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → (Γ ⊢ 𝟙 ∶ 𝒰) ∧ (Γ ⊢ 𝟙 ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · apply HasType.univ_unit hiC
    · apply HasType.univ_unit hiC
    · apply IsType.univ_form hiC

theorem boundary_univ_empty_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → (Γ ⊢ 𝟘 ∶ 𝒰) ∧ (Γ ⊢ 𝟘 ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · apply HasType.univ_empty hiC
    · apply HasType.univ_empty hiC
    · apply IsType.univ_form hiC

theorem boundary_univ_pi_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰)
    → (Γ ⊢ A ∶ 𝒰) ∧ (Γ ⊢ A' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type
    → (Γ ⬝ A ⊢ B ∶ 𝒰) ∧ (Γ ⬝ A ⊢ B' ∶ 𝒰) ∧ Γ ⬝ A ⊢ 𝒰 type
    → (Γ ⊢ ΠA;B ∶ 𝒰) ∧ (Γ ⊢ ΠA';B' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
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
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ≡ B' ∶ 𝒰)
    → (Γ ⊢ A ∶ 𝒰) ∧ (Γ ⊢ A' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type
    → (Γ ⬝ A ⊢ B ∶ 𝒰) ∧ (Γ ⬝ A ⊢ B' ∶ 𝒰) ∧ Γ ⬝ A ⊢ 𝒰 type
    → (Γ ⊢ ΣA;B ∶ 𝒰) ∧ (Γ ⊢ ΣA';B' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
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

theorem boundary_univ_nat_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → (Γ ⊢ 𝒩 ∶ 𝒰) ∧ (Γ ⊢ 𝒩 ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    repeat' apply And.intro
    · apply HasType.univ_nat hiC
    · apply HasType.univ_nat hiC
    · apply IsType.univ_form hiC

theorem boundary_univ_iden_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' a₁ a₂ a₃ a₄ : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⊢ a₁ ≡ a₂ ∶ A)
    → (Γ ⊢ a₃ ≡ a₄ ∶ A)
    → (Γ ⊢ A ∶ 𝒰) ∧ (Γ ⊢ A' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type
    → (Γ ⊢ a₁ ∶ A) ∧ (Γ ⊢ a₂ ∶ A) ∧ Γ ⊢ A type
    → (Γ ⊢ a₃ ∶ A) ∧ (Γ ⊢ a₄ ∶ A) ∧ Γ ⊢ A type
    → (Γ ⊢ a₁ ≃[A] a₃ ∶ 𝒰) ∧ (Γ ⊢ a₂ ≃[A'] a₄ ∶ 𝒰) ∧ Γ ⊢ 𝒰 type :=
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
    (Γ ⊢ a ≡ b ∶ A)
    → Γ ⊢ A ≡ B type
    → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ b ∶ A) ∧ Γ ⊢ A type
    → Γ ⊢ A type ∧ Γ ⊢ B type
    → (Γ ⊢ a ∶ B) ∧ (Γ ⊢ b ∶ B) ∧ Γ ⊢ B type :=
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
    (Γ ⊢ a ≡ a' ∶ A)
    → (Γ ⊢ a ∶ A) ∧ (Γ ⊢ a' ∶ A) ∧ Γ ⊢ A type
    → (Γ ⊢ a' ∶ A) ∧ (Γ ⊢ a ∶ A) ∧ Γ ⊢ A type :=
  by
    intro n Γ a a' A haaA ihaaA
    repeat' apply And.intro
    · apply And.left (And.right ihaaA)
    · apply And.left ihaaA
    · apply And.right (And.right ihaaA)

theorem boundary_term_trans :
    ∀ {n : Nat} {Γ : Ctx n} {T a b c : Tm n},
    (Γ ⊢ a ≡ b ∶ T)
    → (Γ ⊢ b ≡ c ∶ T)
    → (Γ ⊢ a ∶ T) ∧ (Γ ⊢ b ∶ T) ∧ Γ ⊢ T type
    → (Γ ⊢ b ∶ T) ∧ (Γ ⊢ c ∶ T) ∧ Γ ⊢ T type
    → (Γ ⊢ a ∶ T) ∧ (Γ ⊢ c ∶ T) ∧ Γ ⊢ T type :=
  by
    intro n Γ T a b c habT hbcT ihabT ihbcT
    repeat' apply And.intro
    · apply And.left ihabT
    · apply And.left (And.right ihbcT)
    · apply And.right (And.right ihabT)
