import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution

import IMLTT.typed.proofs.admissable.FunctionalityTyping.IsCtx
import IMLTT.typed.proofs.admissable.FunctionalityTyping.IsType
import IMLTT.typed.proofs.admissable.FunctionalityTyping.HasType

set_option pp.proofs true

theorem functionality_typing :
    (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx)
    ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {T : Tm (n + 1)} {s s' S : Tm l},
      (Γ ⊢ s ≡ s' ∶ S)
      → (Γ ⊢ s ∶ S)
      → (Γ ⊢ s' ∶ S)
      → (Γ ⬝ S ⊗ Δ ⊢ T type)
      → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l))
        ⊢ (T⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉)
        ≡ (T⌈s'/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) type)
    ∧ (∀ {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {t T : Tm (n + 1)} {s s' S : Tm l},
      (Γ ⊢ s ≡ s' ∶ S)
      → (Γ ⊢ s ∶ S)
      → (Γ ⊢ s' ∶ S)
      → (Γ ⬝ S ⊗ Δ ⊢ t ∶ T)
      → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l))
        ⊢ (t⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉)
        ≡ (t⌈s'/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉)
        ∶ (T⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉))
    ∧ (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type)
    ∧ (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → (Γ ⊢ a ≡ a' ∶ A)) :=
  by
    suffices h :
      (∀ {n : Nat} {Γ : Ctx n},
        Γ ctx
        → ∀ (m l k : Nat) {leq : l ≤ m}
          (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
          (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
          (Γ_1 ⊢ s ≡ s' ∶ S)
          → (Γ_1 ⊢ s ∶ S)
          → (Γ_1 ⊢ s' ∶ S)
          → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
          → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
      ∧ (∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
          Γ ⊢ A type
          → (∀ (m l k : Nat) {leq : l ≤ m}
            (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
            (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
            (Γ_1 ⊢ s ≡ s' ∶ S)
            → (Γ_1 ⊢ s ∶ S)
            → (Γ_1 ⊢ s' ∶ S)
            → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ
            → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type)
            ∧
            ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1))
              (eqM : n = m + 1),
              (Γ_1 ⊢ s ≡ s' ∶ S) →
                (Γ_1 ⊢ s ∶ S) →
                  (Γ_1 ⊢ s' ∶ S) →
                    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
      (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
          (Γ ⊢ a ∶ A) →
            (∀ (m l k : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1))
                (eqM : n = k + 1) (s s' S : Tm l) (T : Tm (m + 1)),
                (Γ_1 ⊢ s ≡ s' ∶ S) →
                  (Γ_1 ⊢ s ∶ S) →
                    (Γ_1 ⊢ s' ∶ S) →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ ⊙ T ⊗ Ξ → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ T⌈s/ₙleq⌉ ≡ T⌈s'/ₙleq⌉ type) ∧
              ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1))
                (eqM : n = m + 1),
                (Γ_1 ⊢ s ≡ s' ∶ S) →
                  (Γ_1 ⊢ s ∶ S) →
                    (Γ_1 ⊢ s' ∶ S) →
                      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ →
                        eqM ▸ a = t → eqM ▸ A = T → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ t⌈s/ₙleq⌉ ≡ t⌈s'/ₙleq⌉ ∶ T⌈s/ₙleq⌉) ∧
        (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ⊢ A ≡ A' type) ∧
          ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ⊢ a ≡ a' ∶ A

    by
      any_goals repeat' (apply And.intro)
      · intro n Γ hiC
        apply hiC
      · intro n l Γ Δ T s s' S hssS hsS hsS' hT
        have h1 := (And.left (And.right h)) hT
        apply And.right h1
        · apply hssS
        · apply hsS
        · apply hsS'
        · rfl
        · rfl
        · rfl
      · intro n l Γ Δ t T s s' S hssS hsS hsS' htT
        have h1 := (And.left (And.right (And.right h))) htT
        apply And.right h1
        · apply hssS
        · apply hsS
        · apply hsS'
        · rfl
        · rfl
        · rfl
        · rfl
      · intro n Γ A A' hAA
        apply hAA
      · intro n Γ A a a' haaA
        apply haaA
    apply judgment_recursor
      (motive_1 := fun {n} Γ' _hiC =>
        (∀m l k {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) s s' S T,
          (Γ ⊢ s ≡ s' ∶ S)
          → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
          → eqM ▸ Γ' = Γ ⬝ S ⊗ Δ ⊙ T ⊗ Ξ →
          (Γ ⊗ ⌈s⌉(Δ w/(Nat.le_refl l)) ⊢ T⌈s/ₙ (leq)⌉ ≡ T⌈s'/ₙ (leq)⌉ type)))
      (motive_2 := fun {n} Γ' A' _hA =>
        (∀m l k {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) s s' S T,
          (Γ ⊢ s ≡ s' ∶ S)
          → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
          → eqM ▸ Γ' = Γ ⬝ S ⊗ Δ ⊙ T ⊗ Ξ →
          (Γ ⊗ ⌈s⌉(Δ w/(Nat.le_refl l)) ⊢ T⌈s/ₙ (leq)⌉ ≡ T⌈s'/ₙ (leq)⌉ type))
        ∧
        ∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ ⊢ s ≡ s' ∶ S)
        → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ A' = T
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ leq⌉) ≡ (T⌈s'/ₙ leq⌉) type)
      (motive_3 := fun {n} Γ' a' A' haA =>
        (∀m l k {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (Ξ : CtxGen (m + 2) (k + 1)) (eqM : n = k + 1) s s' S T,
          (Γ ⊢ s ≡ s' ∶ S)
          → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
          → eqM ▸ Γ' = Γ ⬝ S ⊗ Δ ⊙ T ⊗ Ξ →
          (Γ ⊗ ⌈s⌉(Δ w/(Nat.le_refl l)) ⊢ T⌈s/ₙ (leq)⌉ ≡ T⌈s'/ₙ (leq)⌉ type))
        ∧
        (∀ (m l : Nat) {leq : l ≤ m} (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (s s' S : Tm l) (t T : Tm (m + 1)) (eqM : n = m + 1),
        (Γ ⊢ s ≡ s' ∶ S)
        → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
        → eqM ▸ Γ' = (Γ ⬝ S ⊗ Δ) → eqM ▸ a' = t → eqM ▸ A' = T
        → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (t⌈s/ₙ leq⌉) ≡ (t⌈s'/ₙ (leq)⌉) ∶ (T⌈s/ₙ (leq)⌉)))
      (motive_4 := fun {n} Γ' C C' _hCC => Γ' ⊢ C ≡ C' type)
      (motive_5 := fun {n} Γ' c c' C _haaA => Γ' ⊢ c ≡ c' ∶ C)
    case IsCtxEmpty =>
       apply functionality_typing_empty
    case IsCtxExtend =>
      apply functionality_typing_extend
    case IsTypeUnitForm =>
      apply functionality_typing_unit_form
    case IsTypeEmptyForm =>
      apply functionality_typing_empty_form
    case IsTypePiForm =>
      apply functionality_typing_pi_form
    case IsTypeSigmaForm =>
      apply functionality_typing_sigma_form
    case IsTypeNatForm =>
      apply functionality_typing_nat_form
    case IsTypeIdenForm =>
      apply functionality_typing_iden_form
    case IsTypeUnivForm =>
      apply functionality_typing_univ_form
    case IsTypeUnivElim =>
      apply functionality_typing_univ_elim
    case HasTypeVar =>
      apply functionality_typing_var
    case HasTypeWeak =>
      apply functionality_typing_weak
    case HasTypeUnitIntro =>
      apply functionality_typing_unit_intro
    case HasTypePiIntro =>
      apply functionality_typing_pi_intro
    case HasTypeSigmaIntro =>
      apply functionality_typing_sigma_intro
    case HasTypeNatZeroIntro =>
      apply functionality_typing_nat_zero_intro
    case HasTypeNatSuccIntro =>
      apply functionality_typing_nat_succ_intro
    case HasTypeIdenIntro =>
      apply functionality_typing_iden_intro
    case HasTypeUnivUnit =>
      apply functionality_typing_univ_unit
    case HasTypeUnivEmpty =>
      apply functionality_typing_univ_empty
    case HasTypeUnivPi =>
      apply functionality_typing_univ_pi
    case HasTypeUnivSigma =>
      apply functionality_typing_univ_sigma
    case HasTypeUnivNat =>
      apply functionality_typing_univ_nat
    case HasTypeUnivIden =>
      apply functionality_typing_univ_iden
    case HasTypeUnitElim =>
      apply functionality_typing_unit_elim
    case HasTypeEmptyElim =>
      apply functionality_typing_empty_elim
    case HasTypePiElim =>
      apply functionality_typing_pi_elim
    case HasTypeSigmaElim =>
      apply functionality_typing_sigma_elim
    case HasTypeNatElim =>
      apply functionality_typing_nat_elim
    case HasTypeIdenElim =>
      apply functionality_typing_iden_elim
    case HasTypeTyConv =>
      apply functionality_typing_ty_conv
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

theorem functionality_typing_general_type {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {T : Tm (n + 1)} {s s' S : Tm l} :
    (Γ ⬝ S ⊗ Δ ⊢ T type)
    → (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
    → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ (T⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) ≡ (T⌈s'/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) type :=
  by
    intro hT hssS hsS hsS'
    apply And.left (And.right functionality_typing) hssS hsS hsS' hT

theorem functionality_typing_general_term {n l : Nat} {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {t T : Tm (n + 1)} {s s' S : Tm l} :
    (Γ ⬝ S ⊗ Δ ⊢ t ∶ T)
    → (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
    → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢
      (t⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) ≡ (t⌈s'/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉)
      ∶ (T⌈s/ₙ (Nat.le_of_succ_le_succ (gen_ctx_leq Δ))⌉) :=
  by
    intro htT hssS hsS hsS'
    apply And.left (And.right (And.right functionality_typing)) hssS hsS hsS' htT

  theorem functionality_typing_type {l : Nat} {Γ : Ctx l} {s s' S : Tm l} {T : Tm (l + 1)} :
      Γ ⬝ S ⊢ T type
      → (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
      → (Γ ⊢ T⌈s⌉₀ ≡ T⌈s'⌉₀ type) :=
  by
    intro hT hssS hsS hsS'
    simp only [substitute_zero]
    simp only [zero_substitution_conv]
    simp only [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right functionality_typing)
    · apply hssS
    · apply hsS
    · apply hsS'
    · apply hT

theorem functionality_typing_term {l : Nat} {Γ : Ctx l} {s s' S : Tm l} {t T : Tm (l + 1)} :
      (Γ ⬝ S ⊢ t ∶ T)
      → (Γ ⊢ s ≡ s' ∶ S) → (Γ ⊢ s ∶ S) → (Γ ⊢ s' ∶ S)
      → (Γ ⊢  t⌈s⌉₀ ≡ t⌈s'⌉₀ ∶ T⌈s⌉₀) :=
  by
    intro htT hssS hsS hsS'
    simp only [substitute_zero]
    simp only [zero_substitution_conv]
    simp only [←n_substitution_zero]
    rw [←empty_expand_context (Γ := Γ)]
    rw [←empty_extend_expand_context_n_substitution]
    apply And.left (And.right (And.right functionality_typing))
    · apply hssS
    · apply hsS
    · apply hsS'
    · apply htT
