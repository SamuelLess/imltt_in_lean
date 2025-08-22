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

import IMLTT.typed.proofs.admissable.Substitution.Helpers

theorem substitution_gen_unit_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → (Γ_1 ⊢ s ∶ S)
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx)
    → ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
    (A : Tm (m + 1 - 1 + 1)),
    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝟙 = A
    → (Γ_1 ⊢ s ∶ S)
    → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A⌈s/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.unit_form
    cases Δ
    case start =>
      apply ctx_decr hiC
    case expand Δ' T =>
      apply ihiC
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_empty_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → (Γ_1 ⊢ s ∶ S)
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx)
    → ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
    (A : Tm (m + 1 - 1 + 1)),
    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝟘 = A
    → (Γ_1 ⊢ s ∶ S)
    → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A⌈s/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.empty_form
    cases Δ
    case start =>
      apply ctx_decr hiC
    case expand Δ' T =>
      apply ihiC
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_pi_form
    {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)}
    (hA : Γ ⊢ A type) (hB : Γ ⬝ A ⊢ B type) :
    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1)
      {s S : Tm l} (A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ type) →
    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1)
      {s S : Tm l} (A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = A_1
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ type)
    → ∀ (m l : Nat) {leq : l ≤ m} (Γn : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
    (T : Tm (m + 1 - 1 + 1)),
    eqM ▸ Γ = Γn ⬝ S ⊗ Δ
    → (eqM ▸ (.pi A B)) = T
    → (Γn ⊢ s ∶ S)
    → (Γn ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ T⌈s/ₙleq⌉ type :=
  by
    intro ihA ihB m l hleq Γ' Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsType.pi_form
    · apply ihA
      repeat' rfl
      apply hsS
    · apply_subst_eq ihB
      repeat' rfl
      apply hsS

theorem substitution_gen_sigma_form
    {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)}
    (a : Γ ⊢ A type) (a_1 : Γ ⬝ A ⊢ B type) :
    (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
      (A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ type)
    → (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n + 1 = m + 1) {s S : Tm l}
      (A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ B = A_1
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ type)
    → ∀ (m l : Nat) {leq : l ≤ m} (Γa : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
    (T : Tm (m + 1 - 1 + 1)),
    eqM ▸ Γ = Γa ⬝ S ⊗ Δ
    → (eqM ▸ ΣA;B) = T
    → (Γa ⊢ s ∶ S)
    → (Γa ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ T⌈s/ₙleq⌉ type :=
  by
    intro ihA ihB m l hleq Γ' Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsType.sigma_form
    · apply ihA
      repeat' rfl
      apply hsS
    · apply_subst_eq ihB
      repeat' rfl
      apply hsS

theorem substitution_gen_nat_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → (Γ_1 ⊢ s ∶ S)
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx)
    → ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
    (A : Tm (m + 1 - 1 + 1)),
    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝒩 = A
    → (Γ_1 ⊢ s ∶ S)
    → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A⌈s/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.nat_form
    cases Δ
    case start =>
      apply ctx_decr hiC
    case expand Δ' T =>
      apply ihiC
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_iden_form :
    ∀ {n : Nat} {Γ : Ctx n} {a A a' : Tm n},
    Γ ⊢ A type
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
        (A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → (Γ_1 ⊢ s ∶ S)
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type)
    → (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a_5 A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a = a_5
      → eqM ▸ A = A_1
      → (Γ_1 ⊢ s ∶ S)
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a_5⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉)
    → (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ a' = a
      → eqM ▸ A = A_1
      → (Γ_1 ⊢ s ∶ S)
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉)
    → ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
        (A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → (eqM ▸ a ≃[A] a') = A_1
      → (Γ_1 ⊢ s ∶ S)
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type :=
  by
    intro n Γ' a A a' hA haA haA' ihA ihaA ihaA' m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    simp [substitute]
    apply IsType.iden_form
    · apply ihA
      · rfl
      · rfl
      · apply hsS
      · rfl
    · apply ihaA
      · rfl
      · rfl
      · rfl
      · exact hsS
      · rfl
    · apply ihaA'
      · rfl
      · rfl
      · rfl
      · exact hsS
      · rfl

theorem substitution_gen_univ_form :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → (Γ_1 ⊢ s ∶ S)
      → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx)
    → ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
      (A : Tm (m + 1 - 1 + 1)),
    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ 𝒰 = A
    → (Γ_1 ⊢ s ∶ S)
    → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A⌈s/ₙleq⌉ type :=
  by
    intro n Γ' hiC ihiC m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.univ_form
    cases Δ
    case start =>
      apply ctx_decr hiC
    case expand Δ' T =>
      apply ihiC
      · rfl
      · apply hsS
      · rfl

theorem substitution_gen_univ_elim : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
    (Γ ⊢ A ∶ 𝒰)
    → (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) (s S : Tm l)
        (a A_1 : Tm (m + 1 - 1 + 1)),
      eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = a
      → eqM ▸ 𝒰 = A_1
      → (Γ_1 ⊢ s ∶ S)
      → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ a⌈s/ₙleq⌉ ∶ A_1⌈s/ₙleq⌉)
    → ∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : n = m + 1) {s S : Tm l}
      (A_1 : Tm (m + 1 - 1 + 1)),
    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A = A_1
    → (Γ_1 ⊢ s ∶ S)
    → (Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⊢ A_1⌈s/ₙleq⌉ type :=
  by
    intro n Γ' A hAU ihAU m l hleq Γ Δ heqM s S T heqΓ heqT hsS
    cases heqM
    cases heqΓ
    cases heqT
    apply IsType.univ_elim
    rw [←substitution_univ]
    apply ihAU
    · rfl
    · rfl
    · rfl
    · apply hsS
    · rfl
