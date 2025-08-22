import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import IMLTT.typed.proofs.admissable.Weakening.IsCtx
import IMLTT.typed.proofs.admissable.Weakening.IsType
import IMLTT.typed.proofs.admissable.Weakening.HasType
import IMLTT.typed.proofs.admissable.Weakening.IsEqualType
import IMLTT.typed.proofs.admissable.Weakening.IsEqualTerm

-- ⇑ₙ↑id > weaken_from
theorem weakening :
  (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {S : Tm l},
    (Γ ⊗ Δ) ctx
    → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ) ctx))
  ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A : Tm n} {S : Tm l},
    (Γ ⊗ Δ) ⊢ A type
    → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ type)
  ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a : Tm n} {S : Tm l},
    ((Γ ⊗ Δ) ⊢ a ∶ A)
    → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋)
  ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A A' : Tm n} {S : Tm l},
    (Γ ⊗ Δ) ⊢ A ≡ A' type
    → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ ≡ A'⌊↑₁n↬l⌋ type)
  ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a a' : Tm n} {S : Tm l},
    ((Γ ⊗ Δ) ⊢ a ≡ a' ∶ A)
    → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ≡ a'⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋) :=
  by
    suffices h :
        (∀ {n : Nat} {Γ : Ctx n},
          Γ ctx
          → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
          Γ_1 ⊢ S type
          → eqM ▸ Γ = Γ_1 ⊗ Δ
          → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
        ∧ (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
          Γ ⊢ A type
          → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
          Γ_1 ⊢ S type
          → eqM ▸ Γ = Γ_1 ⊗ Δ
          → eqM ▸ A = A_1
          → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
        ∧ (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A)
          → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_1 A_1 : Tm m),
          Γ_1 ⊢ S type
          → eqM ▸ Γ = Γ_1 ⊗ Δ
          → eqM ▸ a = a_1
          → eqM ▸ A = A_1
          → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
        ∧ (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
          Γ ⊢ A ≡ A' type
          → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A'_1 : Tm m),
          Γ_1 ⊢ S type
          → eqM ▸ Γ = Γ_1 ⊗ Δ
          → eqM ▸ A = A_1
          → eqM ▸ A' = A'_1
          → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'_1⌊↑₁m↬l⌋ type)
        ∧ ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
          (Γ ⊢ a ≡ a' ∶ A)
          → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_1 a'_1 A_1 : Tm m),
          Γ_1 ⊢ S type
          → eqM ▸ Γ = Γ_1 ⊗ Δ
          → eqM ▸ a = a_1
          → eqM ▸ a' = a'_1
          → eqM ▸ A = A_1
          → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_1⌊↑₁m↬l⌋ ≡ a'_1⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋
      by
        any_goals repeat' (apply And.intro)
        · intro n l Γ Δ S hiC hS
          apply (And.left h)
          · apply hiC
          · apply hS
          · rfl
          · rfl
        · intro n l Γ Δ A S hA hS
          apply And.left (And.right h)
          · apply hA
          · apply hS
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A a S haA hS
          apply And.left (And.right (And.right h))
          · apply haA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A A' S hAA hS
          apply And.left (And.right (And.right (And.right h)))
          · apply hAA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
        · intro n l Γ Δ A a a' S haaA hS
          apply And.right (And.right (And.right (And.right h)))
          · apply haaA
          · apply hS
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ)
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ctx)
      (motive_2 := fun {n} Γ' A' _hA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ A' = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁m↬l⌋ type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S a A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ a' = a → eqM ▸ A' = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (a⌊↑₁m↬l⌋) ∶ (A⌊↑₁m↬l⌋))
      (motive_4 := fun {n} Γ' C C' _hCC =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S A A',
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ C = A → eqM ▸ C' = A'
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (A⌊↑₁m↬l⌋) ≡ (A'⌊↑₁m↬l⌋) type)
      (motive_5 := fun {n} Γ' c c' C _haaA =>
        ∀ m l (Γ : Ctx l) (Δ : CtxGen l m) (eqM : n = m) S a a' A,
        (Γ ⊢ S type)
        → eqM ▸ Γ' = (Γ ⊗ Δ) → eqM ▸ c = a → eqM ▸ c' = a' → eqM ▸ C = A
        → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (a⌊↑₁m↬l⌋) ≡ (a'⌊↑₁m↬l⌋) ∶ (A⌊↑₁m↬l⌋))
    case IsCtxEmpty =>
      apply weakening_gen_empty
    case IsCtxExtend =>
      apply weakening_gen_extend
    case IsTypeUnitForm =>
      apply weakening_unit_form
    case IsTypeEmptyForm =>
      apply weakening_empty_form
    case IsTypePiForm =>
      apply weakening_pi_form
    case IsTypeSigmaForm =>
      apply weakening_sigma_form
    case IsTypeNatForm =>
      apply weakening_nat_form
    case IsTypeIdenForm =>
      apply weakening_iden_form
    case IsTypeUnivForm =>
      apply weakening_univ_form
    case IsTypeUnivElim =>
      apply weakening_univ_elim
    case HasTypeVar =>
      apply weakening_var
    case HasTypeWeak =>
      apply weakening_weak
    case HasTypeUnitIntro =>
      apply weakening_unit_intro
    case HasTypePiIntro =>
      apply weakening_pi_intro
    case HasTypeSigmaIntro =>
      apply weakening_sigma_intro
    case HasTypeNatZeroIntro =>
      apply weakening_nat_zero_intro
    case HasTypeNatSuccIntro =>
      apply weakening_nat_succ_intro
    case HasTypeIdenIntro =>
      apply weakening_iden_intro
    case HasTypeUnivUnit =>
      apply weakening_univ_unit
    case HasTypeUnivEmpty =>
      apply weakening_univ_empty
    case HasTypeUnivPi =>
      apply weakening_univ_pi
    case HasTypeUnivSigma =>
      apply weakening_univ_sigma
    case HasTypeUnivNat =>
      apply weakening_univ_nat
    case HasTypeUnivIden =>
      apply weakening_univ_iden
    case HasTypeUnitElim =>
      apply weakening_unit_elim
    case HasTypeEmptyElim =>
      apply weakening_empty_elim
    case HasTypePiElim =>
      apply weakening_pi_elim
    case HasTypeSigmaElim =>
      apply weakening_sigma_elim
    case HasTypeNatElim =>
      apply weakening_nat_elim
    case HasTypeIdenElim =>
      apply weakening_iden_elim
    case HasTypeTyConv =>
      apply weakening_ty_conv
    case IsEqualTypeUnitFormEq =>
      apply weakening_unit_form_eq
    case IsEqualTypeEmptyFormEq =>
      apply weakening_empty_form_eq
    case IsEqualTypePiFormEq =>
      apply weakening_pi_form_eq
    case IsEqualTypeSigmaFormEq =>
      apply weakening_sigma_form_eq
    case IsEqualTypeNatFormEq =>
      apply weakening_nat_form_eq
    case IsEqualTypeIdenFormEq =>
      apply weakening_iden_form_eq
    case IsEqualTypeUnivFormEq =>
      apply weakening_univ_form_eq
    case IsEqualTypeUnivElimEq =>
      apply weakening_univ_elim_eq
    case IsEqualTypeTypeSymm =>
      apply weakening_type_symm
    case IsEqualTypeTypeTrans =>
      apply weakening_type_trans
    case IsEqualTermVarEq =>
      apply weakening_var_eq
    case IsEqualTermWeakEq =>
      apply weakening_weak_eq
    case IsEqualTermUnitComp =>
      apply weakening_unit_comp
    case IsEqualTermPiComp =>
      apply weakening_pi_comp
    case IsEqualTermSigmaComp =>
      apply weakening_sigma_comp
    case IsEqualTermNatZeroComp =>
      apply weakening_nat_zero_comp
    case IsEqualTermNatSuccComp =>
      apply weakening_nat_succ_comp
    case IsEqualTermIdenComp =>
      apply weakening_iden_comp
    case IsEqualTermUnitIntroEq =>
      apply weakening_unit_intro_eq
    case IsEqualTermUnitElimEq =>
      apply weakening_unit_elim_eq
    case IsEqualTermEmptyElimEq =>
      apply weakening_empty_elim_eq
    case IsEqualTermPiIntroEq =>
      apply weakening_pi_intro_eq
    case IsEqualTermPiElimEq =>
      apply weakening_pi_elim_eq
    case IsEqualTermSigmaIntroEq =>
      apply weakening_sigma_intro_eq
    case IsEqualTermSigmaElimEq =>
      apply weakening_sigma_elim_eq
    case IsEqualTermNatZeroIntroEq =>
      apply weakening_nat_zero_intro_eq
    case IsEqualTermNatSuccIntroEq =>
      apply weakening_nat_succ_intro_eq
    case IsEqualTermNatElimEq =>
      apply weakening_nat_elim_eq
    case IsEqualTermIdenIntroEq =>
      apply weakening_iden_intro_eq
    case IsEqualTermIdenElimEq =>
      apply weakening_iden_elim_eq
    case IsEqualTermUnivUnitEq =>
      apply weakening_univ_unit_eq
    case IsEqualTermUnivEmptyEq =>
      apply weakening_univ_empty_eq
    case IsEqualTermUnivPiEq =>
      apply weakening_univ_pi_eq
    case IsEqualTermUnivSigmaEq =>
      apply weakening_univ_sigma_eq
    case IsEqualTermUnivNatEq =>
      apply weakening_univ_nat_eq
    case IsEqualTermUnivIdenEq =>
      apply weakening_univ_iden_eq
    case IsEqualTermTyConvEq =>
      apply weakening_ty_conv_eq
    case IsEqualTermTermSymm =>
      apply weakening_term_symm
    case IsEqualTermTermTrans =>
      apply weakening_term_trans

theorem weakening_general_context {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {S : Tm l} :
    (Γ ⊗ Δ) ctx → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ) ctx) :=
  by
    intro hiC hS
    apply And.left weakening hiC hS

theorem weakening_general_type {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A : Tm n} {S : Tm l} :
    (Γ ⊗ Δ) ⊢ A type → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ type :=
  by
    intro hA hS
    exact And.left (And.right weakening) hA hS

theorem weakening_general_term {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a : Tm n} {S : Tm l} :
    ((Γ ⊗ Δ) ⊢ a ∶ A) → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋ :=
  by
    intro haA hS
    apply And.left (And.right (And.right weakening)) haA hS

theorem weakening_general_type_eq {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A A' : Tm n} {S : Tm l} :
    (Γ ⊗ Δ) ⊢ A ≡ A' type → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ ≡ A'⌊↑₁n↬l⌋ type :=
  by
    intro hAA hS
    apply And.left (And.right (And.right (And.right weakening))) hAA hS

theorem weakening_general_term_eq {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a a' : Tm n} {S : Tm l} :
    ((Γ ⊗ Δ) ⊢ a ≡ a' ∶ A) → (Γ ⊢ S type)
    → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ≡ a'⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋ :=
  by
    intro haaA hS
    apply And.right (And.right (And.right (And.right weakening))) haaA hS

-- specializations of general weakening theorems

theorem weakening_ctx {n : Nat} {Γ : Ctx n} {A S : Tm n} :
    Γ ⬝ A ctx → Γ ⊢ S type → Γ ⬝ S ⬝ A⌊↑ₚidₚ⌋ ctx :=
  by
    intro hiCA hS
    rw [←empty_expand_context (Γ := Γ ⬝ S)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.left weakening
    · apply hiCA
    · apply hS
    · omega

theorem weakening_type {n : Nat} {Γ : Ctx n} {A B : Tm n} :
    Γ ⊢ A type → Γ ⊢ B type → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro hA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    apply And.left (And.right weakening)
    · apply hA
    · apply hB
    · omega

theorem weakening_term :
    (Γ ⊢ a ∶ A) → Γ ⊢ B type → Γ ⬝ B ⊢ a⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋ :=
  by
    intro haA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    apply And.left (And.right (And.right weakening))
    · apply haA
    · apply hB
    · omega

theorem weakening_type_eq :
    Γ ⊢ A ≡ A' type → Γ ⊢ B type → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ ≡ A'⌊↑ₚidₚ⌋ type :=
  by
    intro hAA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    apply And.left (And.right (And.right (And.right weakening)))
    · apply hAA
    · apply hB
    · omega

theorem weakening_term_eq :
    (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ B type → Γ ⬝ B ⊢ a⌊↑ₚidₚ⌋ ≡ a'⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋ :=
  by
    intro haaA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [←empty_expand_context_weaken_from]
    apply And.right (And.right (And.right (And.right weakening)))
    · apply haaA
    · apply hB
    · omega

-- second one weaken

theorem weakening_second_type {n : Nat} {Γ : Ctx n} {B S : Tm n} {A : Tm (n + 1)} :
    Γ ⬝ S ⊢ A type → Γ ⊢ B type → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ A⌊⇑ₚ↑ₚidₚ⌋ type :=
  by
    intro hA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.left (And.right weakening)
    · apply hA
    · apply hB
    any_goals omega

theorem weakening_second_term {n : Nat} {Γ : Ctx n} {S B : Tm n} {A a : Tm (n + 1)} :
    (Γ ⬝ S ⊢ a ∶ A) → Γ ⊢ B type → Γ ⬝ B ⬝ S⌊↑ₚidₚ⌋ ⊢ a⌊⇑ₚ↑ₚidₚ⌋ ∶ A⌊⇑ₚ↑ₚidₚ⌋ :=
  by
    intro haA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.left (And.right (And.right weakening))
    · apply haA
    · apply hB
    any_goals omega

theorem weakening_second_type_eq {n : Nat} {Γ : Ctx n} {B S : Tm n} {A A' : Tm (n + 1)} :
    Γ ⬝ S ⊢ A ≡ A' type → Γ ⊢ B type
    → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ A⌊⇑ₚ↑ₚidₚ⌋ ≡ A'⌊⇑ₚ↑ₚidₚ⌋ type :=
  by
    intro hAA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.left (And.right (And.right (And.right weakening)))
    · apply hAA
    · apply hB
    any_goals omega

theorem weakening_second_term_eq {n : Nat} {Γ : Ctx n} {B S : Tm n} {a a' A : Tm (n + 1)} :
    (Γ ⬝ S ⊢ a ≡ a' ∶ A) → Γ ⊢ B type
    → Γ ⬝ B ⬝ (S⌊↑ₚidₚ⌋) ⊢ a⌊⇑ₚ↑ₚidₚ⌋ ≡ a'⌊⇑ₚ↑ₚidₚ⌋ ∶ A⌊⇑ₚ↑ₚidₚ⌋ :=
  by
    intro haaA hB
    rw [←empty_expand_context (Γ := Γ ⬝ B)]
    rw [←weaken_from_zero]
    rw [lift_weaken_from]
    rw [←empty_expand_context_weaken_from]
    rw [extend_expand_context_weaken_from]
    apply And.right (And.right (And.right (And.right weakening)))
    · apply haaA
    · apply hB
    any_goals omega







theorem useWeakTypewithWeak :
    (Γ ⊢ A type) → Γ ⊢ B type → A' = A⌊↑ₚidₚ⌋ → Γ ⬝ B ⊢ A' type :=
  by
    intro haA hB heqA
    cases heqA
    apply weakening_type
    repeat' assumption

theorem useWeakTermwithWeak :
    (Γ ⊢ a ∶ A) → Γ ⊢ B type → a' = a⌊↑ₚidₚ⌋ → A' = A⌊↑ₚidₚ⌋ → Γ ⬝ B ⊢ a' ∶ A' :=
  by
    intro haA hB heqa heqA
    cases heqa
    cases heqA
    apply weakening_term
    repeat' assumption

-- theorem test_new_weaken_from {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A : Tm n} {S : Tm l} :
--     (Γ ⊗ Δ) ⊢ A type → (Γ ⊢ S type)
--     → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊lift_weak_n (n - l) (↑ₚ(idₚ : Weak l l))⌋ type :=
--   by
--     sorry

-- mutual
--   theorem weakening_general_context_t {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {S : Tm l} :
--       (Γ ⊗ Δ) ctx → (Γ ⊢ S type)
--       → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ) ctx) :=
--     by
--       intro hiC hS
--       cases Δ with
--       | start =>
--         cases hiC with
--         | empty =>
--           simp []
--           apply IsCtx.extend IsCtx.empty hS
--         | extend hiC hA =>
--           simp []
--           apply IsCtx.extend
--           · apply IsCtx.extend hiC hA
--           · apply hS
--       | expand Δ' A =>
--         cases hiC with
--         | extend hiC hA =>
--           simp []
--           apply IsCtx.extend
--           · apply weakening_general_context_t
--             apply hiC
--             apply hS
--           · apply weakening_general_type_t
--             apply hA
--             apply hS
--     termination_by Γ
--
--   theorem weakening_general_type_t {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A : Tm n} {S : Tm l} :
--       (Γ ⊗ Δ) ⊢ A type → (Γ ⊢ S type)
--       → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ type :=
--     by
--       intro hA hS
--       cases hA with
--       | unit_form hiC =>
--         apply IsType.unit_form
--         apply weakening_general_context_t
--         apply hiC
--         apply hS
--       | iden_form hA haA haA' =>
--         apply IsType.iden_form
--         · apply weakening_general_type_t
--           apply hA
--           apply hS
--         · apply weakening_general_term_t
--           apply haA
--           apply hS
--         · apply weakening_general_term_t
--           apply haA'
--           apply hS
--       | _ => sorry
--     termination_by Γ
--
--   theorem weakening_general_term_t {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a : Tm n} {S : Tm l} :
--       ((Γ ⊗ Δ) ⊢ a ∶ A) → (Γ ⊢ S type)
--       → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋ :=
--     by
--       intro haA hS
--       cases Δ with
--       | start =>
--         cases haA with
--         | var hA =>
--           substitution_norm
--           have h := HasType.weak (HasType.var hA) hS
--           replace_by_conclusion h
--           · substitution_norm
--           · apply h
--         | _ =>
--           sorry
--       | expand Δ A =>
--         cases haA with
--         | var hA =>
--           substitution_norm
--           simp [←weakening_shift_id]
--           rw [weakening_id]
--           apply HasType.var
--           apply weakening_general_type_t
--           apply hA
--           apply hS
--         | weak hvA hB =>
--           substitution_norm
--           simp [←weakening_shift_id]
--           rw [weakening_id]
--           apply HasType.weak
--           · rw [←weakening_conv_var]
--             apply weakening_general_term_t
--             apply hvA
--             apply hS
--           · apply weakening_general_type_t
--             apply hB
--             apply hS
--           | ty_conv haA hAB =>
--             apply HasType.ty_conv
--             · apply weakening_general_term_t
--               apply haA
--               apply hS
--             · apply weakening_general_type_eq_t
--               apply hAB
--               apply hS
--         | _ =>
--           sorry
--     termination_by Γ
--
--   theorem weakening_general_type_eq_t {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A A' : Tm n} {S : Tm l} :
--       (Γ ⊗ Δ) ⊢ A ≡ A' type → (Γ ⊢ S type)
--       → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ ≡ A'⌊↑₁n↬l⌋ type :=
--     by
--       intro hAA hS
--       sorry
--     termination_by Γ
-- end

-- theorem weakening' :
--   (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {S : Tm l},
--     (Γ ⊗ Δ) ctx
--     → (Γ ⊢ S type)
--     → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ) ctx))
--   ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A : Tm n} {S : Tm l},
--     (Γ ⊗ Δ) ⊢ A type
--     → (Γ ⊢ S type)
--     → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ type)
--   ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a : Tm n} {S : Tm l},
--     ((Γ ⊗ Δ) ⊢ a ∶ A)
--     → (Γ ⊢ S type)
--     → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋)
--   ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A A' : Tm n} {S : Tm l},
--     (Γ ⊗ Δ) ⊢ A ≡ A' type
--     → (Γ ⊢ S type)
--     → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A⌊↑₁n↬l⌋ ≡ A'⌊↑₁n↬l⌋ type)
--   ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen l n} {A a a' : Tm n} {S : Tm l},
--     ((Γ ⊗ Δ) ⊢ a ≡ a' ∶ A)
--     → (Γ ⊢ S type)
--     → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ a⌊↑₁n↬l⌋ ≡ a'⌊↑₁n↬l⌋ ∶ A⌊↑₁n↬l⌋) :=
--   by
--     suffices h :
--         (∀ {n : Nat} {Γ : Ctx n},
--             Γ ctx →
--               ∀ (l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l n) (S : Tm l), Γ_1 ⊢ S type → Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊⇑ₙ↑₁l⌋Δ) ctx) ∧
--           (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
--               Γ ⊢ A type →
--                 ∀ (l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l n) (S : Tm l),
--                   Γ_1 ⊢ S type → Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊⇑ₙ↑₁l⌋Δ) ⊢ A⌊⇑ₙn⊖l↑₁⌋ type) ∧
--             (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
--                 (Γ ⊢ a ∶ A) →
--                   ∀ (l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l n) (S : Tm l),
--                     Γ_1 ⊢ S type → Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊⇑ₙ↑₁l⌋Δ) ⊢ a⌊⇑ₙn⊖l↑₁⌋ ∶ A⌊⇑ₙn⊖l↑₁⌋) ∧
--               (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
--                   Γ ⊢ A ≡ A' type →
--                     ∀ (l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l n) (S : Tm l),
--                       Γ_1 ⊢ S type → Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊⇑ₙ↑₁l⌋Δ) ⊢ A⌊⇑ₙn⊖l↑₁⌋ ≡ A'⌊⇑ₙn⊖l↑₁⌋ type) ∧
--                 ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
--                   (Γ ⊢ a ≡ a' ∶ A) →
--                     ∀ (l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l n) (S : Tm l),
--                       Γ_1 ⊢ S type → Γ = Γ_1 ⊗ Δ → (Γ_1 ⬝ S ⊗ ⌊⇑ₙ↑₁l⌋Δ) ⊢ a⌊⇑ₙn⊖l↑₁⌋ ≡ a'⌊⇑ₙn⊖l↑₁⌋ ∶ a⌊⇑ₙn⊖l↑₁⌋
--       by
--         repeat' apply And.intro
--         · intro n l Γ Δ S hiC hS
--           apply And.left h
--           apply hiC
--           apply hS
--           rfl
--         · intro n l Γ Δ A S hA hS
--           apply And.left (And.right h)
--           apply hA
--           apply hS
--           rfl
--         · intro n l Γ Δ A a S haA hS
--           apply And.left (And.right (And.right h))
--           apply haA
--           apply hS
--           rfl
--         · intro n l Γ Δ A A' S hAA hS
--           apply And.left (And.right (And.right (And.right h)))
--           apply hAA
--           apply hS
--           rfl
--         · intro n l Γ Δ A a A' S haaA hS
--           apply And.right (And.right (And.right (And.right h)))
--           apply haaA
--           apply hS
--           rfl
--     apply judgment_recursor
--       (motive_1 := fun {n} Γ' _hiC =>
--         ∀ l (Γ : Ctx l) (Δ : CtxGen l n) S,
--         (Γ ⊢ S type)
--         → Γ' = (Γ ⊗ Δ)
--         → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ctx)
--       (motive_2 := fun {n} Γ' A' _hA =>
--         ∀ l (Γ : Ctx l) (Δ : CtxGen l n) S,
--         (Γ ⊢ S type)
--         → Γ' = (Γ ⊗ Δ)
--         → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ A'⌊↑₁n↬l⌋ type)
--       (motive_3 := fun {n} Γ' a' A' haA =>
--         ∀ l (Γ : Ctx l) (Δ : CtxGen l n) S,
--         (Γ ⊢ S type)
--         → Γ' = (Γ ⊗ Δ)
--         → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (a'⌊↑₁n↬l⌋) ∶ (A'⌊↑₁n↬l⌋))
--       (motive_4 := fun {n} Γ' C C' _hCC =>
--         ∀ l (Γ : Ctx l) (Δ : CtxGen l n) S,
--         (Γ ⊢ S type)
--         → Γ' = (Γ ⊗ Δ)
--         → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (C⌊↑₁n↬l⌋) ≡ (C'⌊↑₁n↬l⌋) type)
--       (motive_5 := fun {n} Γ' c c' C _haaA =>
--         ∀ l (Γ : Ctx l) (Δ : CtxGen l n) S,
--         (Γ ⊢ S type)
--         → Γ' = (Γ ⊗ Δ)
--         → (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⊢ (c⌊↑₁n↬l⌋) ≡ (c'⌊↑₁n↬l⌋) ∶ (c⌊↑₁n↬l⌋))
--     any_goals sorry
