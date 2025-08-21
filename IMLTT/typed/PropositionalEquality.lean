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

import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

theorem pi_same_type_diff_var_context_iden_weak :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))
              ⊢ (Π(P⌊↑ₚidₚ⌋);(P⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(0)⌉⌊↑ₚidₚ⌋))⌊↑ₚidₚ⌋ type :=
  by
    intro hP
    have hA := ctx_extr (boundary_ctx_type hP)
    apply weakening_type
    · apply IsType.pi_form
      · apply weakening_type
        · apply hP
        · apply weakening_type hA hA
      · apply weakening_type
        · apply_subst_eq weakening_second_type hP hA
        · apply weakening_type
          · apply hP
          · apply weakening_type hA hA
    · apply IsType.iden_form
      · rw (config := {occs := .pos [1]}) [←weakening_shift_id]
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        apply weakening_type
        · apply weakening_type
          · apply hA
          · apply hA
        · rw [weakening_id]
          apply weakening_type
          · apply hA
          · apply hA
      · rw [weakening_shift_vone]
        rw (config := {occs := .pos [3]}) [←weakening_shift_id]
        apply HasType.weak
        · apply HasType.var hA
        · apply weakening_type
          · apply hA
          · apply hA
      · rw (config := {occs := .pos [2]}) [←weakening_shift_id]
        apply HasType.var
        apply weakening_type
        · apply hA
        · apply hA

theorem inhabitant_pi_same_type_diff_val :
    (Γ ⬝ A ⊢ P type)
    → Γ ⬝ A ⊢ λP; v(0) ∶ ΠP;P⌊↑ₚidₚ⌋ :=
  by
    intro hP
    apply HasType.pi_intro (HasType.var hP)

theorem leibniz_principle {n : Nat} {Γ : Ctx n} {A p a a' h : Tm n} {P : Tm (n + 1)} :
    (Γ ⬝ A ⊢ P type)
    → (Γ ⊢ p ∶ a ≃[A] a')
    → (Γ ⊢ h ∶ P⌈a⌉₀)
    → ∃h', (Γ ⊢ h' ∶ P⌈a'⌉₀)
    :=
  by
    intro hP hpId hhP
    have hA := ctx_extr (boundary_ctx_type hP)
    have hId := boundary_term_type hpId
    have hIdInv := iden_is_type_inversion hId
    apply Exists.intro
    have hB := pi_same_type_diff_var_context_iden_weak hP
    have hbB := inhabitant_pi_same_type_diff_val hP
    have hElimId := HasType.iden_elim hB (by apply_subst_eq hbB)
                    (And.left (And.right hIdInv)) (And.right (And.right hIdInv)) hpId
    have hElimPi :=
      by
        apply HasType.pi_elim
        rotate_left
        · apply hhP
        rotate_right
        · apply_subst_eq hElimId
    · apply_subst_eq hElimPi

theorem propositional_equality_symm :
    (Γ ⊢ p ∶ a ≃[A] a')
    → ∃p', (Γ ⊢ p' ∶ a' ≃[A] a) :=
  by
    intro hpId
    have hId := boundary_term_type hpId
    have hIdInv := iden_is_type_inversion hId
    have hA := And.left hIdInv
    have hP : Γ ⬝ A ⊢ v(0) ≃[A⌊↑ₚidₚ⌋] a⌊↑ₚidₚ⌋ type :=
      by
        apply IsType.iden_form
        · apply weakening_type hA hA
        · apply HasType.var hA
        · apply weakening_term (And.left (And.right hIdInv)) hA
    have hreflId : Γ ⊢ .refl A a ∶ (a ≃[A] a) :=
      by
        apply HasType.iden_intro
        · apply hA
        · apply And.left (And.right hIdInv)
    · apply_subst_eq leibniz_principle hP hpId
      · apply_subst_eq hreflId

theorem propositional_equality_trans :
    (Γ ⊢ p₁ ∶ a₁ ≃[A] a₂)
    → (Γ ⊢ p₂ ∶ a₂ ≃[A] a₃)
    → ∃p, (Γ ⊢ p ∶ a₁ ≃[A] a₃) :=
  by
    intro hpId hpId'
    have hId := boundary_term_type hpId
    have hIdInv := iden_is_type_inversion hId
    have hId' := boundary_term_type hpId'
    have hIdInv' := iden_is_type_inversion hId'
    have hA := And.left hIdInv
    have hP : Γ ⬝ A ⊢ a₁⌊↑ₚidₚ⌋ ≃[A⌊↑ₚidₚ⌋] v(0) type :=
      by
        apply IsType.iden_form
        · apply weakening_type hA hA
        · apply weakening_term (And.left (And.right hIdInv)) hA
        · apply HasType.var hA
    · apply_subst_eq leibniz_principle hP hpId'
      · apply_subst_eq hpId
