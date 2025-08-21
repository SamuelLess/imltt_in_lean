import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Contexts
import IMLTT.untyped.proofs.Mixture

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.RulesEquality
import IMLTT.typed.proofs.Recursor
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import IMLTT.typed.proofs.admissable.Weakening.Helpers

theorem weakening_var :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x + 1 = m) (S : Tm l) (a A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
    → eqM ▸ v(0) = a
    → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A hA ihA m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqt
    cases heqT
    cases Δ with
    | start =>
      cases heqΓ
      have h := HasType.weak (HasType.var hA) hS
      apply_subst_eq h
    | expand Δ' S' =>
      cases heqΓ
      apply_subst_eq HasType.var
      apply ihA
      apply hS
      any_goals rfl

theorem weakening_weak :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ∶ A)
    → Γ ⊢ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ v(i) = a
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋) →
    (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x = m) (S : Tm l) (A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ B = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : x + 1 = m) (S : Tm l) (a A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ ⬝ B = Γ_1 ⊗ Δ
    → eqM ▸ v(i)⌊↑ₚidₚ⌋ = a
    → eqM ▸ A⌊↑ₚidₚ⌋ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n x Γ A B hvA hB ihvA ihB m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqt
    cases heqT
    cases Δ with
    | start =>
      cases heqΓ
      apply_subst_eq HasType.weak
      · apply HasType.weak
        · apply hvA
        · apply hB
      · apply hS
    | expand Δ' S' =>
      cases heqΓ
      apply_subst_eq HasType.weak
      · substitution_step_meta
        rw (config := {occs := .pos [2]}) [←weakening_shift_id]
      · simp []
        rw [←weakening_conv_var]
        apply ihvA
        apply hS
        repeat' rfl
      · apply ihB
        apply hS
        repeat' rfl

theorem weakening_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ ⋆ = a
    → eqM ▸ 𝟙 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ' hiC ihiC m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.unit_intro
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ∶ B)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ λA; b) = a
    → (eqM ▸ ΠA;B) = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ' A b B hbB ihbB m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.pi_intro
    apply_subst_eq ihbB
    rw [extend_expand_context_weaken_from]
    apply hS
    repeat' rfl

theorem weakening_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ∶ A)
    → (Γ ⊢ b ∶ B⌈a⌉₀)
    → Γ ⬝ A ⊢ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_4 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_4⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ b = a_5
      → eqM ▸ B⌈a⌉₀ = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_7 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a&b = a_7
      → (eqM ▸ ΣA;B) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_7⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ a A b B haA hbB hB ihaA ihbB ihB m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.sigma_intro
    · apply ihaA
      apply hS
      repeat' rfl
    · apply_subst_eq ihbB
      apply hS
      repeat' rfl
    · apply_subst_eq ihB
      rw [extend_expand_context_weaken_from]
      apply hS
      repeat' rfl

theorem weakening_nat_zero_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝓏 = a
    → eqM ▸ 𝒩 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ hiC ihiC m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.nat_zero_intro
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_nat_succ_intro :
    ∀ {n : Nat} {Γ : Ctx n} {x : Tm n},
    (Γ ⊢ x ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ x = a
      → eqM ▸ 𝒩 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝓈(x) = a
    → eqM ▸ 𝒩 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ x hxNat ihxNat m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.nat_succ_intro
    rw [←weakening_nat]
    apply ihxNat
    apply hS
    repeat' rfl

theorem weakening_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
    Γ ⊢ A type
    → (Γ ⊢ a ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_4 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_4⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A.refl a = a_5
      → (eqM ▸ a ≃[A] a) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A a hA haA ihA ihaA m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.iden_intro
    · apply ihA
      apply hS
      repeat' rfl
    · apply ihaA
      apply hS
      repeat' rfl

theorem weakening_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝟙 = a
    → eqM ▸ 𝒰 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ hiC ihiC m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_unit
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝟘 = a
    → eqM ▸ 𝒰 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ hiC ihiC m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_empty
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ∶ 𝒰)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = a
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ ΠA;B) = a
    → eqM ▸ 𝒰 = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A B hAU hBU ihAU ihBU m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_pi
    · rw [←weakening_univ]
      apply ihAU
      apply hS
      repeat' rfl
    · apply_subst_eq ihBU
      rw (config := {occs := .pos [1]}) [extend_expand_context_weaken_from]
      rw [←weakening_univ]
      apply hS
      rw [extend_expand_context]
      repeat' rfl

theorem weakening_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ∶ 𝒰)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ B = a
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ ΣA;B) = a
    → eqM ▸ 𝒰 = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A B hAU hBU ihAU ihBU m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_sigma
    · rw [←weakening_univ]
      apply ihAU
      apply hS
      repeat' rfl
    · apply_subst_eq ihBU
      rw (config := {occs := .pos [1]}) [extend_expand_context_weaken_from]
      rw [←weakening_univ]
      apply hS
      repeat' rfl

theorem weakening_univ_nat :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ctx)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ 𝒩 = a
    → eqM ▸ 𝒰 = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ hiC ihiC m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_nat
    apply ihiC
    apply hS
    repeat' rfl

theorem weakening_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_5
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a' = a
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_7 A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → (eqM ▸ a ≃[A] a') = a_7
    → eqM ▸ 𝒰 = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_7⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A a a' hAU haA haA' ihAU ihaA ihaA' m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.univ_iden
    · rw [←weakening_univ]
      apply ihAU
      apply hS
      repeat' rfl
    · apply ihaA
      apply hS
      repeat' rfl
    · apply ihaA'
      apply hS
      repeat' rfl

theorem weakening_unit_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type
    → (Γ ⊢ a ∶ A⌈⋆⌉₀)
    → (Γ ⊢ b ∶ 𝟙)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝟙 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_5
      → eqM ▸ A⌈⋆⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ 𝟙 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_7 A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indUnit b a = a_7
    → eqM ▸ A⌈b⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_7⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A a b hA haA hb1 ihA ihaA ihb1 m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_weak]
    apply HasType.unit_elim
    · apply_subst_eq ihA
      rw [←weakening_unit]
      rw [←extend_expand_context_weaken_from]
      apply hS
      repeat' rfl
    · apply_subst_eq ihaA
      simp []
      rw [←weakening_tt, substitution_zero_weak_simp]
      apply hS
      repeat' rfl
    · rw [←weakening_unit]
      apply ihb1
      apply hS
      repeat' rfl

theorem weakening_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
    Γ ⬝ 𝟘 ⊢ A type
    → (Γ ⊢ b ∶ 𝟘)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝟘 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ 𝟘 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indEmpty b = a
    → eqM ▸ A⌈b⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A b hA hb0 ihA ihb0 m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_weak]
    apply HasType.empty_elim
    · rw [←weakening_empty]
      rw [extend_expand_context_weaken_from]
      apply use_equality_type
      apply ihA
      apply hS
      rw [extend_expand_context]
      substitution_step_meta
      substitution_step_meta
    · rw [←weakening_empty]
      apply ihb0
      apply hS
      repeat' rfl

theorem weakening_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
    (Γ ⊢ f ∶ ΠA;B)
    → (Γ ⊢ a ∶ A)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ f = a
      → (eqM ▸ ΠA;B) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_4 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_4
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_4⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ f◃a = a_5
    → eqM ▸ B⌈a⌉₀ = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ f A B a hfPi haA ihfPi ihaA m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_weak]
    apply HasType.pi_elim
    · rw [←weakening_pi]
      apply ihfPi
      apply hS
      repeat' rfl
    · apply ihaA
      apply hS
      repeat' rfl

theorem weakening_sigma_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
    (Γ ⬝ ΣA;B) ⊢ C type
    → (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
    → (Γ ⊢ p ∶ ΣA;B)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → (eqM ▸ Γ ⬝ ΣA;B) = Γ_1 ⊗ Δ
      → eqM ▸ C = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A ⬝ B = Γ_1 ⊗ Δ
      → eqM ▸ c = a
      → eqM ▸ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ p = a
      → (eqM ▸ ΣA;B) = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.indSigma B C c p = a
    → eqM ▸ C⌈p⌉₀ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A B p C c hC hcC hpSi ihC ihcC ihpSi m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_weak]
    apply HasType.sigma_elim
    · apply use_equality_type
      apply ihC
      apply hS
      rw [extend_expand_context]
      substitution_step_meta
      substitution_step_meta
    · apply use_equality_term
      apply ihcC
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
      any_goals substitution_step_meta
      substitution_norm
    · apply use_equality_term
      apply ihpSi
      apply hS
      substitution_step_meta

theorem weakening_nat_elim :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ∶ 𝒩)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝒩 = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ z = a
      → eqM ▸ A⌈𝓏⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ 𝒩 ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ s = a
      → eqM ▸ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ x = a
      → eqM ▸ 𝒩 = A
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A.indNat z s x = a
      → eqM ▸ A⌈x⌉₀ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ z x A s hA hzA hsA hxA ihA ihzA ihsA ihxA m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [substitution_zero_weak]
    apply HasType.nat_elim
    · apply use_equality_type
      apply ihA
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
    · apply use_equality_term
      apply ihzA
      apply hS
      any_goals substitution_step_meta
      any_goals substitution_norm
    · apply use_equality_term
      apply ihsA
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
      any_goals substitution_step_meta
      substitution_norm
    · rw [←weakening_nat]
      apply ihxA
      apply hS
      repeat' rfl

theorem weakening_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a a' p : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
    → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → (Γ ⊢ p ∶ a ≃[A] a')
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 + 1 + 1 = m) (S : Tm l) (A_1 : Tm m),
      Γ_1 ⊢ S type
      → (eqM ▸ Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) = Γ_1 ⊗ Δ
      → eqM ▸ B = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ type)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n + 1 = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ ⬝ A = Γ_1 ⊗ Δ
      → eqM ▸ b = a
      → eqM ▸ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_6 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_6
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_6⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a' = a
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_8 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ p = a_8
      → (eqM ▸ a ≃[A] a') = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_8⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_9 A_1 : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ A.j B b a a' p = a_9
    → eqM ▸ B⌈(ₛidₚ)⋄ a⋄ a'⋄ p⌉ = A_1
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_9⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋ :=
  by
    intro n Γ A B b a a' p hB hbB haA haA' hpId ihB ihbB ihaA ihaA' ihpId
    intro m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    rw [helper_weakening_iden_elim_B]
    apply HasType.iden_elim
    · apply use_equality_type
      apply ihB
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
      any_goals substitution_norm
    · apply use_equality_term
      apply ihbB
      apply hS
      simp only [extend_expand_context]
      any_goals substitution_step_meta
    · apply ihaA
      apply hS
      repeat' rfl
    · apply ihaA'
      apply hS
      repeat' rfl
    · rw [←weakening_iden]
      apply ihpId
      apply hS
      repeat' rfl

theorem weakening_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
    (Γ ⊢ a ∶ A)
    → Γ ⊢ A ≡ B type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_3 A_1 : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ a = a_3
      → eqM ▸ A = A_1
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_3⌊↑₁m↬l⌋ ∶ A_1⌊↑₁m↬l⌋)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (A_1 A' : Tm m),
      Γ_1 ⊢ S type
      → eqM ▸ Γ = Γ_1 ⊗ Δ
      → eqM ▸ A = A_1
      → eqM ▸ B = A'
      → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ A_1⌊↑₁m↬l⌋ ≡ A'⌊↑₁m↬l⌋ type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen l m) (eqM : n = m) (S : Tm l) (a_5 A : Tm m),
    Γ_1 ⊢ S type
    → eqM ▸ Γ = Γ_1 ⊗ Δ
    → eqM ▸ a = a_5
    → eqM ▸ B = A
    → (Γ_1 ⬝ S ⊗ ⌊↑₁↬l⌋Δ) ⊢ a_5⌊↑₁m↬l⌋ ∶ A⌊↑₁m↬l⌋ :=
  by
    intro n Γ a A B haA hAB ihaA ihAB m l Γ Δ heqM S t T hS heqΓ heqt heqT
    cases heqM
    cases heqΓ
    cases heqt
    cases heqT
    apply HasType.ty_conv
    · apply ihaA
      apply hS
      repeat' rfl
    · apply ihAB
      apply hS
      repeat' rfl
