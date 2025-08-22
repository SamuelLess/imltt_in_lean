import IMLTT.typed.JudgmentsAndRules
import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

notation:100 A "⌊⌋" => shift_tm A
theorem ida (hAtype : Γ ⊢ A type) : Γ ⊢ λA; v(0) ∶ Π A; A⌊⌋ := by
  apply HasType.pi_intro
  apply HasType.var
  exact hAtype

theorem ida' (hAtype : Γ ⊢ A type) : Γ ⊢ λA; v(0) ∶ Π A; A⌊⌋ := by
  aesop
/- wishlist for DSL:
from
hAtype : Γ ⊢ A type
derive
Γ ⊢ λA; v(0) ∶ A -> A
-/

-- Tm
/-
theorem subst_var (T : Tm n) : Γ ⊢ (T⌊↑ₚidₚ⌋)⌈v(0)⌉₀ ≃ T := by
  simp_all only [substitute_zero, substitution_shift_substitute_zero_simp]
  sorry
  apply HasType.var
  apply weakening_type (HasType.var (by simp)) (HasType.var (by simp))-/

theorem subst_shift {s A : Tm n} : A⌊↑ₚidₚ⌋⌈s⌉₀ = A := by exact
  substitution_shift_substitute_zero

theorem eqs : A⌊↑ₚ↑ₚidₚ⌋⌈s⌉₀ = A⌊↑ₚidₚ⌋⌊↑ₚidₚ⌋⌈s⌉₀ := by simp
theorem eqs' {n : Nat} {A : Tm n} {ρ : Weak (m+1) n} {ρ' : Weak (m) n} :
    A⌊ρ⌋⌈s⌉₀ = A⌊ρ'⌋⌊↑ₚidₚ⌋⌈s⌉₀ := by sorry

theorem subst_shift'' {s : Tm (n+1)} {A : Tm (n)} : A⌊↑ₚ↑ₚidₚ⌋⌈s⌉₀ = A⌊⌋ := by
  rw [eqs]
  exact subst_shift


theorem comp {A B C : Tm n} (hAtype : Γ ⊢ A type) (hBtype : Γ ⊢ B type) (hCtype : Γ ⊢ C type) :
    Γ ⊢ λΠB;C⌊↑ₚidₚ⌋;(λΠA⌊↑ₚidₚ⌋;B⌊↑ₚ↑ₚidₚ⌋;λA⌊↑ₚ↑ₚidₚ⌋; v(2)◃(v(1)◃v(0)))
      ∶ Π(ΠB;C⌊↑ₚidₚ⌋);(Π(ΠA⌊↑ₚidₚ⌋;B⌊↑ₚ↑ₚidₚ⌋);(ΠA⌊↑ₚ↑ₚidₚ⌋;C⌊↑ₚ↑ₚ↑ₚidₚ⌋)) := by
  repeat apply HasType.pi_intro

  let Γ' := ((Γ ⬝ ΠB;C⌊↑ₚidₚ⌋) ⬝ ΠA⌊↑ₚidₚ⌋;B⌊↑ₚ↑ₚidₚ⌋) ⬝ A⌊↑ₚ↑ₚidₚ⌋

  have hfirst : (Γ' ⊢ v(2) ∶ ΠB⌊↑ₚ↑ₚ↑ₚidₚ⌋;C⌊↑ₚ↑ₚ↑ₚ↑ₚidₚ⌋) := sorry
  have hsecond : (Γ' ⊢ v(1)◃v(0) ∶ B⌊↑ₚ↑ₚ↑ₚidₚ⌋) := sorry

  have hpielim := @HasType.pi_elim _ _ _ _ _ (v(1)◃v(0)) hfirst hsecond
  sorry
  --rw [subst_shift''] at hpielim

#check HasType.pi_elim

  --apply HasType.pi_elim (f:=v(2))

#check (v(0)⌈𝓏⌉₀ : Tm _)

#check shift_tm
