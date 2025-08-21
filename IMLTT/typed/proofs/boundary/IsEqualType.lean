import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.admissable.ContextConversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem boundary_unit_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
   Γ ctx
   → Γ ctx
   → Γ ⊢ 𝟙 type ∧ Γ ⊢ 𝟙 type :=
  by
    intro n Γ hiC ihiC
    apply And.intro
    · apply IsType.unit_form hiC
    · apply IsType.unit_form hiC

theorem boundary_empty_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → Γ ⊢ 𝟘 type ∧ Γ ⊢ 𝟘 type :=
  by
    intro n Γ hiC ihiC
    apply And.intro
    · apply IsType.empty_form hiC
    · apply IsType.empty_form hiC

theorem boundary_pi_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    Γ ⊢ A ≡ A' type
    → Γ ⬝ A ⊢ B ≡ B' type
    → Γ ⊢ A type ∧ Γ ⊢ A' type
    → Γ ⬝ A ⊢ B type ∧ Γ ⬝ A ⊢ B' type
    → Γ ⊢ ΠA;B type ∧ Γ ⊢ ΠA';B' type :=
  by
    intro n Γ A A' B B' hAA hBB ihAA ihBB
    apply And.intro
    · apply IsType.pi_form
      · apply And.left ihAA
      · apply And.left ihBB
    · apply IsType.pi_form
      · apply And.right ihAA
      · apply context_conversion_type
        · apply And.right ihAA
        · apply hAA
        · apply And.right ihBB

theorem boundary_sigma_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n} {B B' : Tm (n + 1)},
    Γ ⊢ A ≡ A' type
    → Γ ⬝ A ⊢ B ≡ B' type
    → Γ ⊢ A type ∧ Γ ⊢ A' type
    → Γ ⬝ A ⊢ B type ∧ Γ ⬝ A ⊢ B' type
    → Γ ⊢ ΣA;B type ∧ Γ ⊢ ΣA';B' type :=
  by
    intro n Γ A A' B B' hAA hBB ihAA ihBB
    apply And.intro
    · apply IsType.sigma_form
      · apply And.left ihAA
      · apply And.left ihBB
    · apply IsType.sigma_form
      · apply And.right ihAA
      · apply context_conversion_type
        · apply And.right ihAA
        · apply hAA
        · apply And.right ihBB

theorem boundary_nat_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → Γ ⊢ 𝒩 type ∧ Γ ⊢ 𝒩 type :=
  by
    intro n Γ hiC ihiC
    apply And.intro
    · apply IsType.nat_form hiC
    · apply IsType.nat_form hiC

theorem boundary_iden_form_eq :
    ∀ {n : Nat} {Γ : Ctx n} {a₁ a₂ A a₃ a₄ A' : Tm n},
    Γ ⊢ A ≡ A' type
    → (Γ ⊢ a₁ ≡ a₂ ∶ A)
    → (Γ ⊢ a₃ ≡ a₄ ∶ A')
    → Γ ⊢ A type ∧ Γ ⊢ A' type
    → (Γ ⊢ a₁ ∶ A) ∧ (Γ ⊢ a₂ ∶ A) ∧ Γ ⊢ A type
    → (Γ ⊢ a₃ ∶ A') ∧ (Γ ⊢ a₄ ∶ A') ∧ Γ ⊢ A' type
    → Γ ⊢ a₁ ≃[A] a₃ type ∧ Γ ⊢ a₂ ≃[A'] a₄ type :=
  by
    intro n Γ a₁ a₂ A a₃ a₄ A' hAA haaA haaA' ihAA ihaaA ihaaA'
    apply And.intro
    · apply IsType.iden_form
      · apply And.left ihAA
      · apply And.left ihaaA
      · apply HasType.ty_conv (And.left ihaaA') (IsEqualType.type_symm hAA)
    · apply IsType.iden_form
      · apply And.right ihAA
      · apply HasType.ty_conv (And.left (And.right ihaaA)) hAA
      · apply And.left (And.right ihaaA')

theorem boundary_univ_form_eq :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → Γ ⊢ 𝒰 type ∧ Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    apply And.intro
    · apply IsType.univ_form hiC
    · apply IsType.univ_form hiC

theorem boundary_univ_elim_eq :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    (Γ ⊢ A ≡ A' ∶ 𝒰)
    → (Γ ⊢ A ∶ 𝒰) ∧ (Γ ⊢ A' ∶ 𝒰) ∧ Γ ⊢ 𝒰 type
    → Γ ⊢ A type ∧ Γ ⊢ A' type :=
  by
    intro n Γ' A A' hAAU ihAAU
    apply And.intro
    · apply IsType.univ_elim (And.left ihAAU)
    · apply IsType.univ_elim (And.left (And.right ihAAU))

theorem boundary_type_symm :
    ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    Γ ⊢ A ≡ A' type
    → Γ ⊢ A type ∧ Γ ⊢ A' type
    → Γ ⊢ A' type ∧ Γ ⊢ A type :=
  by
    intro n Γ A A' hAA ihAA
    apply And.intro
    · apply And.right ihAA
    · apply And.left ihAA

theorem boundary_type_trans :
    ∀ {n : Nat} {Γ : Ctx n} {A B C : Tm n},
    Γ ⊢ A ≡ B type
    → Γ ⊢ B ≡ C type
    → Γ ⊢ A type ∧ Γ ⊢ B type
    → Γ ⊢ B type ∧ Γ ⊢ C type
    → Γ ⊢ A type ∧ Γ ⊢ C type :=
  by
    intro n Γ A B C hAB hBC ihAB ihBC
    apply And.intro
    · apply And.left ihAB
    · apply And.right ihBC
