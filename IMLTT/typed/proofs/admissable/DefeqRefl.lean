import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Contexts
import IMLTT.untyped.proofs.Contexts

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor

import IMLTT.typed.proofs.admissable.DefeqRefl.IsCtx
import IMLTT.typed.proofs.admissable.DefeqRefl.IsType
import IMLTT.typed.proofs.admissable.DefeqRefl.HasType

theorem defeq_refl :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ⊢ A ≡ A type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → (Γ ⊢ a ≡ a ∶ A)) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
    (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A))
  :=
  by
    suffices h :
      (∀ {n : Nat} {Γ : Ctx n},
        Γ ctx
        → ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
        Γ ⊢ A type
        → (∀ (eqM : n = 0) (A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ A = A_1 → ε ⊢ A_1 ≡ A_1 type)
          ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type)
          ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (A_1 : Tm z) (B : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type)
      ∧ (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
        (Γ ⊢ a ∶ A)
        → (∀ (eqM : n = 0) (a_1 A_1 : Tm 0), eqM ▸ Γ = ε → eqM ▸ a = a_1 → eqM ▸ A = A_1 → ε ⊢ a_1 ≡ a_1 ∶ A_1)
          ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (B : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → Γ_1 ⊢ B ≡ B type)
          ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) (a_1 A_1 : Tm z) (B : Tm m),
            eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ a = a_1 → eqM ▸ A = A_1 → Γ_1 ⬝ B ⊗ Δ ⊢ a_1 ≡ a_1 ∶ A_1)
      ∧ (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type)
      ∧ ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ≡ a' ∶ A
    by
      any_goals repeat' apply And.intro
      · intro n Γ hiC
        apply hiC
      · intro n Γ A hA
        have ihA := And.left (And.right h) hA
        have ihεAA := And.left ihA
        have ihΓBB := And.left (And.right ihA)
        have ihΓAA := And.right (And.right ihA)
        cases Γ with
        | empty =>
          apply ihεAA
          · rfl
          · rfl
          · rfl
        | extend Γ S =>
          rw [←empty_expand_context (Γ := Γ ⬝ S)]
          apply ihΓAA
          · rfl
          · rfl
          · rfl
      · intro n Γ A a haA
        have ihaA := And.left (And.right (And.right h)) haA
        cases Γ with
        | empty =>
          apply And.left ihaA
          any_goals rfl
        | extend Γ S =>
          simp_all
          rw [←empty_expand_context (Γ := Γ ⬝ S)]
          apply And.right ihaA
          any_goals rfl
      · intro n Γ A A' hAA
        apply hAA
      · intro n Γ a a' A haaA
        apply haaA
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        (∀m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ →
          (Γ ⊢ B ≡ B type)))
      (motive_2 := fun {n} Γ' A' _hA =>
        (∀ (eqM : n = 0) A,
          eqM ▸ Γ' = ε → eqM ▸ A' = A →
          (ε ⊢ A ≡ A type)) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ →
          Γ ⊢ B ≡ B type) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) A B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ A' = A →
          (Γ ⬝ B ⊗ Δ ⊢ A ≡ A type)))
      (motive_3 := fun {n} Γ' a' A' _haA =>
        (∀ (eqM : n = 0) a A,
          eqM ▸ Γ' = ε → eqM ▸ a' = a → eqM ▸ A' = A →
          (ε ⊢ a ≡ a ∶ A)) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ →
          Γ ⊢ B ≡ B type) ∧
        (∀ m z (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : n = z) a A B,
          eqM ▸ Γ' = Γ ⬝ B ⊗ Δ → eqM ▸ a' = a → eqM ▸ A' = A →
          (Γ ⬝ B  ⊗ Δ ⊢ a ≡ a ∶ A))
      )
      (motive_4 := fun Γ A A' _hAA => Γ ⊢ A ≡ A' type)
      (motive_5 := fun Γ a a' A _haaA => Γ ⊢ a ≡ a' ∶ A)
    case IsCtxEmpty =>
      apply defeq_refl_empty
    case IsCtxExtend =>
      apply defeq_refl_extend
    case IsTypeUnitForm =>
      apply defeq_refl_unit_form
    case IsTypeEmptyForm =>
      apply defeq_refl_empty_form
    case IsTypePiForm =>
      apply defeq_refl_pi_form
    case IsTypeSigmaForm =>
      apply defeq_refl_sigma_form
    case IsTypeNatForm =>
      apply defeq_refl_nat_form
    case IsTypeIdenForm =>
      apply defeq_refl_iden_form
    case IsTypeUnivForm =>
      apply defeq_refl_univ_form
    case IsTypeUnivElim =>
      apply defeq_refl_univ_elim
    case HasTypeVar =>
      apply defeq_refl_var
    case HasTypeWeak =>
      apply defeq_refl_weak
    case HasTypeUnitIntro =>
      apply defeq_refl_unit_intro
    case HasTypePiIntro =>
      apply defeq_refl_pi_intro
    case HasTypeSigmaIntro =>
      apply defeq_refl_sigma_intro
    case HasTypeNatZeroIntro =>
      apply defeq_refl_nat_zero_intro
    case HasTypeNatSuccIntro =>
      apply defeq_refl_nat_succ_intro
    case HasTypeIdenIntro =>
      apply defeq_refl_iden_intro
    case HasTypeUnivUnit =>
      apply defeq_refl_univ_unit
    case HasTypeUnivEmpty =>
      apply defeq_refl_univ_empty
    case HasTypeUnivPi =>
      apply defeq_refl_univ_pi
    case HasTypeUnivSigma =>
      apply defeq_refl_univ_sigma
    case HasTypeUnivNat =>
      apply defeq_refl_univ_nat
    case HasTypeUnivIden =>
      apply defeq_refl_univ_iden
    case HasTypeUnitElim =>
      apply defeq_refl_unit_elim
    case HasTypeEmptyElim =>
      apply defeq_refl_empty_elim
    case HasTypePiElim =>
      apply defeq_refl_pi_elim
    case HasTypeSigmaElim =>
      apply defeq_refl_sigma_elim
    case HasTypeNatElim =>
      apply defeq_refl_nat_elim
    case HasTypeIdenElim =>
      apply defeq_refl_iden_elim
    case HasTypeTyConv =>
      apply defeq_refl_ty_conv
    case IsEqualTypeUnitFormEq =>
      repeat' intro
      apply IsEqualType.unit_form_eq
      assumption
    case IsEqualTypeEmptyFormEq =>
      repeat' intro
      apply IsEqualType.empty_form_eq
      assumption
    case IsEqualTypePiFormEq =>
      repeat' intro
      apply IsEqualType.pi_form_eq
      repeat' assumption
    case IsEqualTypeSigmaFormEq =>
      repeat' intro
      apply IsEqualType.sigma_form_eq
      repeat' assumption
    case IsEqualTypeNatFormEq =>
      repeat' intro
      apply IsEqualType.nat_form_eq
      repeat' assumption
    case IsEqualTypeIdenFormEq =>
      repeat' intro
      apply IsEqualType.iden_form_eq
      repeat' assumption
    case IsEqualTypeUnivFormEq =>
      repeat' intro
      apply IsEqualType.univ_form_eq
      repeat' assumption
    case IsEqualTypeUnivElimEq =>
      repeat' intro
      apply IsEqualType.univ_elim_eq
      repeat' assumption
    case IsEqualTypeTypeSymm =>
      repeat' intro
      apply IsEqualType.type_symm
      repeat' assumption
    case IsEqualTypeTypeTrans =>
      repeat' intro
      apply IsEqualType.type_trans
      repeat' assumption
    case IsEqualTermVarEq =>
      repeat' intro
      apply IsEqualTerm.var_eq
      repeat' assumption
    case IsEqualTermWeakEq =>
      repeat' intro
      apply IsEqualTerm.weak_eq
      repeat' assumption
    case IsEqualTermUnitComp =>
      repeat' intro
      apply IsEqualTerm.unit_comp
      repeat' assumption
    case IsEqualTermPiComp =>
      repeat' intro
      apply IsEqualTerm.pi_comp
      repeat' assumption
    case IsEqualTermSigmaComp =>
      repeat' intro
      apply IsEqualTerm.sigma_comp
      repeat' assumption
    case IsEqualTermNatZeroComp =>
      repeat' intro
      apply IsEqualTerm.nat_zero_comp
      repeat' assumption
    case IsEqualTermNatSuccComp =>
      repeat' intro
      apply IsEqualTerm.nat_succ_comp
      repeat' assumption
    case IsEqualTermIdenComp =>
      repeat' intro
      apply IsEqualTerm.iden_comp
      repeat' assumption
    case IsEqualTermUnitIntroEq =>
      repeat' intro
      apply IsEqualTerm.unit_intro_eq
      repeat' assumption
    case IsEqualTermUnitElimEq =>
      repeat' intro
      apply IsEqualTerm.unit_elim_eq
      repeat' assumption
    case IsEqualTermEmptyElimEq =>
      repeat' intro
      apply IsEqualTerm.empty_elim_eq
      repeat' assumption
    case IsEqualTermPiIntroEq =>
      repeat' intro
      apply IsEqualTerm.pi_intro_eq
      repeat' assumption
    case IsEqualTermPiElimEq =>
      repeat' intro
      apply IsEqualTerm.pi_elim_eq
      repeat' assumption
    case IsEqualTermSigmaIntroEq =>
      repeat' intro
      apply IsEqualTerm.sigma_intro_eq
      repeat' assumption
    case IsEqualTermSigmaElimEq =>
      repeat' intro
      apply IsEqualTerm.sigma_elim_eq
      repeat' assumption
    case IsEqualTermNatZeroIntroEq =>
      repeat' intro
      apply IsEqualTerm.nat_zero_intro_eq
      repeat' assumption
    case IsEqualTermNatSuccIntroEq =>
      repeat' intro
      apply IsEqualTerm.nat_succ_intro_eq
      repeat' assumption
    case IsEqualTermNatElimEq =>
      repeat' intro
      apply IsEqualTerm.nat_elim_eq
      repeat' assumption
    case IsEqualTermIdenIntroEq =>
      repeat' intro
      apply IsEqualTerm.iden_intro_eq
      repeat' assumption
    case IsEqualTermIdenElimEq =>
      repeat' intro
      apply IsEqualTerm.iden_elim_eq
      repeat' assumption
    case IsEqualTermUnivUnitEq =>
      repeat' intro
      apply IsEqualTerm.univ_unit_eq
      repeat' assumption
    case IsEqualTermUnivEmptyEq =>
      repeat' intro
      apply IsEqualTerm.univ_empty_eq
      repeat' assumption
    case IsEqualTermUnivPiEq =>
      repeat' intro
      apply IsEqualTerm.univ_pi_eq
      repeat' assumption
    case IsEqualTermUnivSigmaEq =>
      repeat' intro
      apply IsEqualTerm.univ_sigma_eq
      repeat' assumption
    case IsEqualTermUnivNatEq =>
      repeat' intro
      apply IsEqualTerm.univ_nat_eq
      repeat' assumption
    case IsEqualTermUnivIdenEq =>
      repeat' intro
      apply IsEqualTerm.univ_iden_eq
      repeat' assumption
    case IsEqualTermTyConvEq =>
      repeat' intro
      apply IsEqualTerm.ty_conv_eq
      repeat' assumption
    case IsEqualTermTermSymm =>
      repeat' intro
      apply IsEqualTerm.term_symm
      repeat' assumption
    case IsEqualTermTermTrans =>
      repeat' intro
      apply IsEqualTerm.term_trans
      repeat' assumption

theorem defeq_refl_type : IsType Γ A → IsEqualType Γ A A :=
  by
    intro hA
    apply (And.left (And.right defeq_refl))
    apply hA

theorem defeq_refl_term : HasType Γ a A → IsEqualTerm Γ a a A :=
  by
    intro haA
    have h := (And.left (And.right (And.right defeq_refl))) haA
    apply h
