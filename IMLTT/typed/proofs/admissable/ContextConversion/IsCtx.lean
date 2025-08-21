import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.boundary.BoundaryIsCtx
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution


theorem context_conversion_empty :
    ∀ (m l : Nat) (Γ : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : 0 = m) {S S' : Tm l},
    Γ ⊢ S ≡ S' type
    → Γ ⊢ S type
    → Γ ⊢ S' type
    → eqM ▸ ε = Γ ⬝ S ⊗ Δ
    → Γ ⬝ S' ⊗ Δ ctx  :=
  by
    intro m l Γ Δ heqM S S' hSS hS hS' heqΓ
    cases heqM
    cases Δ

theorem context_conversion_extend :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ctx
    → Γ ⊢ A type
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) {S S' : Tm l},
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → Γ_1 ⬝ S' ⊗ Δ ctx)
    → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x = m) {S S' : Tm l} (A_1 : Tm m),
      Γ_1 ⊢ S ≡ S' type
      → Γ_1 ⊢ S type
      → Γ_1 ⊢ S' type
      → eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
      → eqM ▸ A = A_1
      → Γ_1 ⬝ S' ⊗ Δ ⊢ A_1 type)
    → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) m) (eqM : x + 1 = m) {S S' : Tm l},
    Γ_1 ⊢ S ≡ S' type
    → Γ_1 ⊢ S type
    → Γ_1 ⊢ S' type
    → eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
    → Γ_1 ⬝ S' ⊗ Δ ctx :=
  by
    intro n Γ' A' hiC hA ihiC ihA m l Γ Δ heqM S S' hSS hS hS' heqΓ
    cases heqM
    cases Δ with
    | start =>
      cases heqΓ
      simp [expand_ctx]
      apply IsCtx.extend
      · apply hiC
      · apply hS'
    | expand Δ' T =>
      cases heqΓ
      apply IsCtx.extend
      · apply ihiC
        · apply hSS
        · apply hS
        · apply hS'
        repeat' rfl
      · apply ihA
        · apply hSS
        · apply hS
        · apply hS'
        repeat' rfl
