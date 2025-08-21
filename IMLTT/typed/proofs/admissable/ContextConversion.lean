import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

import IMLTT.typed.proofs.admissable.ContextConversion.IsCtx
import IMLTT.typed.proofs.admissable.ContextConversion.IsType
import IMLTT.typed.proofs.admissable.ContextConversion.HasType
import IMLTT.typed.proofs.admissable.ContextConversion.IsEqualType
import IMLTT.typed.proofs.admissable.ContextConversion.IsEqualTerm

import Aesop

theorem context_conversion :
  (∀ {n : Nat} {Γ : Ctx n},
    Γ ctx → Γ ctx)
  ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {A : Tm n} {S S' : Tm l},
    (Γ ⬝ S ⊗ Δ) ⊢ A type
    → Γ ⊢ S ≡ S' type
    → Γ ⊢ S type
    → Γ ⊢ S' type
    → (Γ ⬝ S' ⊗ Δ) ⊢ A type)
  ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {a A : Tm n} {S S' : Tm l},
    ((Γ ⬝ S ⊗ Δ) ⊢ a ∶ A)
    → Γ ⊢ S ≡ S' type
    → Γ ⊢ S type
    → Γ ⊢ S' type
    → (Γ ⬝ S' ⊗ Δ) ⊢ a ∶ A)
  ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {A A' : Tm n} {S S' : Tm l},
    (Γ ⬝ S ⊗ Δ) ⊢ A ≡ A' type
    → Γ ⊢ S ≡ S' type
    → Γ ⊢ S type
    → Γ ⊢ S' type
    → (Γ ⬝ S' ⊗ Δ) ⊢ A ≡ A' type)
  ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {a a' A : Tm n} {S S' : Tm l},
    ((Γ ⬝ S ⊗ Δ) ⊢ a ≡ a' ∶ A)
    → Γ ⊢ S ≡ S' type
    → Γ ⊢ S type
    → Γ ⊢ S' type
    → (Γ ⬝ S' ⊗ Δ) ⊢ a ≡ a' ∶ A) :=
  by
    suffices h :
      (∀ {n : Nat} {Γ : Ctx n},
        Γ ctx
        → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l},
        Γ_1 ⊢ S ≡ S' type
        → Γ_1 ⊢ S type
        → Γ_1 ⊢ S' type
        → eqM ▸ Γ = (Γ_1 ⬝ S ⊗ Δ)
        → (Γ_1 ⬝ S' ⊗ Δ) ctx)
      ∧ (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type
        → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) {S S' : Tm l} (A_1 : Tm m),
        Γ_1 ⊢ S ≡ S' type
        → Γ_1 ⊢ S type
        → Γ_1 ⊢ S' type
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = A_1
        → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
      ∧ (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
        (Γ ⊢ a ∶ A)
        → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_1 A_1 : Tm m),
        Γ_1 ⊢ S ≡ S' type
        → Γ_1 ⊢ S type
        → Γ_1 ⊢ S' type
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = a_1
        → eqM ▸ A = A_1
        → Γ_1 ⬝ S' ⊗ Δ ⊢ a_1 ∶ A_1)
      ∧ (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
        Γ ⊢ A ≡ A' type
        → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (A_1 A'_1 : Tm m),
        Γ_1 ⊢ S ≡ S' type
        → Γ_1 ⊢ S type
        → Γ_1 ⊢ S' type
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ A = A_1
        → eqM ▸ A' = A'_1
        → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 ≡ A'_1 type)
      ∧ ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
        (Γ ⊢ a ≡ a' ∶ A)
        → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : n = m) (S S' : Tm l) (a_1 a'_1 A_1 : Tm m),
        Γ_1 ⊢ S ≡ S' type
        → Γ_1 ⊢ S type
        → Γ_1 ⊢ S' type
        → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
        → eqM ▸ a = a_1
        → eqM ▸ a' = a'_1
        → eqM ▸ A = A_1
        → Γ_1 ⬝ S' ⊗ Δ ⊢ a_1 ≡ a'_1 ∶ A_1
      by
        repeat' apply And.intro
        · intro n Γ hiC
          apply hiC
        · intro n l Γ Δ A S S' hA hSS hS hS'
          apply And.left (And.right h)
          · apply hA
          · apply hSS
          · apply hS
          · apply hS'
          repeat' rfl
        · intro n l Γ Δ a A S S' haA hSS hS hS'
          apply And.left (And.right (And.right h))
          · apply haA
          · apply hSS
          · apply hS
          · apply hS'
          repeat' rfl
        · intro n l Γ Δ A A' S S' hAA hSS hS hS'
          apply And.left (And.right (And.right (And.right h)))
          · apply hAA
          · apply hSS
          · apply hS
          · apply hS'
          repeat' rfl
        · intro n l Γ Δ a a' A S S' haaA hSS hS hS'
          apply And.right (And.right (And.right (And.right h)))
          · apply haaA
          · apply hSS
          · apply hS
          · apply hS'
          repeat' rfl
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) {S S' : Tm l},
        Γ ⊢ S ≡ S' type
        → Γ ⊢ S type
        → Γ ⊢ S' type
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ)
        → (Γ ⬝ S' ⊗ Δ) ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) {S S' : Tm l} A,
        Γ ⊢ S ≡ S' type
        → Γ ⊢ S type
        → Γ ⊢ S' type
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ)
        → eqM ▸ A' = A
        → (Γ ⬝ S' ⊗ Δ) ⊢ A type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) S S' a A,
        Γ ⊢ S ≡ S' type
        → Γ ⊢ S type
        → Γ ⊢ S' type
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ)
        → eqM ▸ a' = a
        → eqM ▸ A' = A
        → (Γ ⬝ S' ⊗ Δ) ⊢ a ∶ A)
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) S S' A A',
        Γ ⊢ S ≡ S' type
        → Γ ⊢ S type
        → Γ ⊢ S' type
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ)
        → eqM ▸ C = A
        → eqM ▸ C' = A'
        → (Γ ⬝ S' ⊗ Δ) ⊢ A ≡ A' type)
      (motive_5 := fun {n} Γ' c c' C _haaA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen (l + 1) (m)) (eqM : n = m) S S' a a' A,
        Γ ⊢ S ≡ S' type
        → Γ ⊢ S type
        → Γ ⊢ S' type
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ)
        → eqM ▸ c = a
        → eqM ▸ c' = a'
        → eqM ▸ C = A
        → (Γ ⬝ S' ⊗ Δ) ⊢ a ≡ a' ∶ A)
    case IsCtxEmpty =>
      apply context_conversion_empty
    case IsCtxExtend =>
      apply context_conversion_extend
    case IsTypeUnitForm =>
      apply context_conversion_unit_form
    case IsTypeEmptyForm =>
      apply context_conversion_empty_form
    case IsTypePiForm =>
      apply context_conversion_pi_form
    case IsTypeSigmaForm =>
      apply context_conversion_sigma_form
    case IsTypeNatForm =>
      apply context_conversion_nat_form
    case IsTypeIdenForm =>
      apply context_conversion_iden_form
    case IsTypeUnivForm =>
      apply context_conversion_univ_form
    case IsTypeUnivElim =>
      apply context_conversion_univ_elim
    case HasTypeVar =>
      apply context_conversion_var
    case HasTypeWeak =>
      apply context_conversion_weak
    case HasTypeUnitIntro =>
      apply context_conversion_unit_intro
    case HasTypePiIntro =>
      apply context_conversion_pi_intro
    case HasTypeSigmaIntro =>
      apply context_conversion_sigma_intro
    case HasTypeNatZeroIntro =>
      apply context_conversion_nat_zero_intro
    case HasTypeNatSuccIntro =>
      apply context_conversion_nat_succ_intro
    case HasTypeIdenIntro =>
      apply context_conversion_iden_intro
    case HasTypeUnivUnit =>
      apply context_conversion_univ_unit
    case HasTypeUnivEmpty =>
      apply context_conversion_univ_empty
    case HasTypeUnivPi =>
      apply context_conversion_univ_pi
    case HasTypeUnivSigma =>
      apply context_conversion_univ_sigma
    case HasTypeUnivNat =>
      apply context_conversion_univ_nat
    case HasTypeUnivIden =>
      apply context_conversion_univ_iden
    case HasTypeUnitElim =>
      apply context_conversion_unit_elim
    case HasTypeEmptyElim =>
      apply context_conversion_empty_elim
    case HasTypePiElim =>
      apply context_conversion_pi_elim
    case HasTypeSigmaElim =>
      apply context_conversion_sigma_elim
    case HasTypeNatElim =>
      apply context_conversion_nat_elim
    case HasTypeIdenElim =>
      apply context_conversion_iden_elim
    case HasTypeTyConv =>
      apply context_conversion_ty_conv
    case IsEqualTypeUnitFormEq =>
      apply context_conversion_unit_form_eq
    case IsEqualTypeEmptyFormEq =>
      apply context_conversion_empty_form_eq
    case IsEqualTypePiFormEq =>
      apply context_conversion_pi_form_eq
    case IsEqualTypeSigmaFormEq =>
      apply context_conversion_sigma_form_eq
    case IsEqualTypeNatFormEq =>
      apply context_conversion_nat_form_eq
    case IsEqualTypeIdenFormEq =>
      apply context_conversion_iden_form_eq
    case IsEqualTypeUnivFormEq =>
      apply context_conversion_univ_form_eq
    case IsEqualTypeUnivElimEq =>
      apply context_conversion_univ_elim_eq
    case IsEqualTypeTypeSymm =>
      apply context_conversion_type_symm
    case IsEqualTypeTypeTrans =>
      apply context_conversion_type_trans
    case IsEqualTermVarEq =>
      apply context_conversion_var_eq
    case IsEqualTermWeakEq =>
      apply context_conversion_weak_eq
    case IsEqualTermUnitComp =>
      apply context_conversion_unit_comp
    case IsEqualTermPiComp =>
      apply context_conversion_pi_comp
    case IsEqualTermSigmaComp =>
      apply context_conversion_sigma_comp
    case IsEqualTermNatZeroComp =>
      apply context_conversion_nat_zero_comp
    case IsEqualTermNatSuccComp =>
      apply context_conversion_nat_succ_comp
    case IsEqualTermIdenComp =>
      apply context_conversion_iden_comp
    case IsEqualTermUnitIntroEq =>
      apply context_conversion_unit_intro_eq
    case IsEqualTermUnitElimEq =>
      apply context_conversion_unit_elim_eq
    case IsEqualTermEmptyElimEq =>
      apply context_conversion_empty_elim_eq
    case IsEqualTermPiIntroEq =>
      apply context_conversion_pi_intro_eq
    case IsEqualTermPiElimEq =>
      apply context_conversion_pi_elim_eq
    case IsEqualTermSigmaIntroEq =>
      apply context_conversion_sigma_intro_eq
    case IsEqualTermSigmaElimEq =>
      apply context_conversion_sigma_elim_eq
    case IsEqualTermNatZeroIntroEq =>
      apply context_conversion_nat_zero_intro_eq
    case IsEqualTermNatSuccIntroEq =>
      apply context_conversion_nat_succ_intro_eq
    case IsEqualTermNatElimEq =>
      apply context_conversion_nat_elim_eq
    case IsEqualTermIdenIntroEq =>
      apply context_conversion_iden_intro_eq
    case IsEqualTermIdenElimEq =>
      apply context_conversion_iden_elim_eq
    case IsEqualTermUnivUnitEq =>
      apply context_conversion_univ_unit_eq
    case IsEqualTermUnivEmptyEq =>
      apply context_conversion_univ_empty_eq
    case IsEqualTermUnivPiEq =>
      apply context_conversion_univ_pi_eq
    case IsEqualTermUnivSigmaEq =>
      apply context_conversion_univ_sigma_eq
    case IsEqualTermUnivNatEq =>
      apply context_conversion_univ_nat_eq
    case IsEqualTermUnivIdenEq =>
      apply context_conversion_univ_iden_eq
    case IsEqualTermTyConvEq =>
      apply context_conversion_ty_conv_eq
    case IsEqualTermTermSymm =>
      apply context_conversion_term_symm
    case IsEqualTermTermTrans =>
      apply context_conversion_term_trans

theorem context_conv_is_ctx :
    Γ ⊢ A' type
    → Γ ⬝ A ctx → Γ ⊢ A ≡ A' type
    → Γ ⬝ A' ctx :=
  by
    intro hA' hiCA hAA
    match hiCA with
    | .extend hiC _ =>
        apply IsCtx.extend
        · apply hiC
        · apply hA'

theorem context_conversion_type :
    Γ ⊢ A' type → Γ ⊢ A ≡ A' type
    → Γ ⬝ A ⊢ B type
    → Γ ⬝ A' ⊢ B type :=
  by
    intro hA' hAA hB
    rw [←empty_expand_context (Γ := Γ ⬝ A')]
    apply And.left (And.right context_conversion)
    · apply hB
    · apply hAA
    · apply ctx_extr (boundary_ctx_type hB)
    · apply hA'

theorem context_conversion_term :
    Γ ⊢ A' type → Γ ⊢ A ≡ A' type
    → (Γ ⬝ A ⊢ b ∶ B)
    → (Γ ⬝ A' ⊢ b ∶ B) :=
  by
    intro hA' hAA hbB
    rw [←empty_expand_context (Γ := Γ ⬝ A')]
    apply And.left (And.right (And.right context_conversion))
    · apply hbB
    · apply hAA
    · apply ctx_extr (boundary_ctx_term hbB)
    · apply hA'

theorem context_conversion_type_eq :
    Γ ⊢ A' type → Γ ⊢ A ≡ A' type
    → Γ ⬝ A ⊢ B ≡ B' type
    → Γ ⬝ A' ⊢ B ≡ B' type :=
  by
    intro hA' hAA hBB
    rw [←empty_expand_context (Γ := Γ ⬝ A')]
    apply And.left (And.right (And.right (And.right context_conversion)))
    · apply hBB
    · apply hAA
    · apply ctx_extr (boundary_ctx_type_eq hBB)
    · apply hA'


theorem context_conversion_term_eq :
    Γ ⊢ A' type → Γ ⊢ A ≡ A' type
    → (Γ ⬝ A ⊢ b ≡ b' ∶ B)
    → (Γ ⬝ A' ⊢ b ≡ b' ∶ B) :=
  by
    intro hA' hAA hbbB
    rw [←empty_expand_context (Γ := Γ ⬝ A')]
    apply And.right (And.right (And.right (And.right context_conversion)))
    · apply hbbB
    · apply hAA
    · apply ctx_extr (boundary_ctx_term_eq hbbB)
    · apply hA'

theorem context_conversion_general_type :
    (Γ ⬝ S ⊗ Δ) ⊢ A type → Γ ⊢ S ≡ S' type → Γ ⊢ S type → Γ ⊢ S' type
    → (Γ ⬝ S' ⊗ Δ) ⊢ A type :=
  by
    apply And.left (And.right context_conversion)

theorem context_conversion_general_term :
    ((Γ ⬝ S ⊗ Δ) ⊢ a ∶ A) → Γ ⊢ S ≡ S' type → Γ ⊢ S type → Γ ⊢ S' type
    → (Γ ⬝ S' ⊗ Δ) ⊢ a ∶ A :=
  by
    apply And.left (And.right (And.right context_conversion))

theorem context_conversion_general_type_eq :
    (Γ ⬝ S ⊗ Δ) ⊢ A ≡ A' type → Γ ⊢ S ≡ S' type → Γ ⊢ S type → Γ ⊢ S' type
    → (Γ ⬝ S' ⊗ Δ) ⊢ A ≡ A' type :=
  by
    apply And.left (And.right (And.right (And.right context_conversion)))

theorem context_conversion_general_term_eq :
    ((Γ ⬝ S ⊗ Δ) ⊢ a ≡ a' ∶ A) → Γ ⊢ S ≡ S' type → Γ ⊢ S type → Γ ⊢ S' type
    → (Γ ⬝ S' ⊗ Δ) ⊢ a ≡ a' ∶ A :=
  by
    apply And.right (And.right (And.right (And.right context_conversion)))
