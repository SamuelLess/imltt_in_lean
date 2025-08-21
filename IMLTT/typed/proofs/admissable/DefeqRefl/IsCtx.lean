import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Contexts
import IMLTT.untyped.proofs.Contexts

import IMLTT.typed.JudgmentsAndRules

theorem defeq_refl_empty :
   ∀ (m z : Nat) (Γ : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : 0 = z) (B : Tm m),
   eqM ▸ ε = Γ ⬝ B ⊗ Δ
   → Γ ⊢ B ≡ B type
 :=
  by
    intro m z Γ Δ heqM
    have h := gen_ctx_leq Δ
    cases heqM
    omega

theorem defeq_refl_extend :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ctx
    → Γ ⊢ A type
    → (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (B : Tm m),
      eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
      → Γ_1 ⊢ B ≡ B type)
    → ((∀ (eqM : x = 0) (A_1 : Tm 0),
        eqM ▸ Γ = ε
        → eqM ▸ A = A_1
        → ε ⊢ A_1 ≡ A_1 type)
      ∧ (∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ
        → Γ_1 ⊢ B ≡ B type)
      ∧ ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x = z) (A_1 : Tm z) (B : Tm m),
        eqM ▸ Γ = Γ_1 ⬝ B ⊗ Δ → eqM ▸ A = A_1
        → Γ_1 ⬝ B ⊗ Δ ⊢ A_1 ≡ A_1 type)
    → ∀ (m z : Nat) (Γ_1 : Ctx m) (Δ : CtxGen (m + 1) z) (eqM : x + 1 = z) (B : Tm m),
    eqM ▸ Γ ⬝ A = Γ_1 ⬝ B ⊗ Δ
    → Γ_1 ⊢ B ≡ B type :=
  by
    intro n Γ' A hiC hA ihiC ihA
    intro m z Γ Δ heqM S heqΓ
    cases heqM
    cases Δ with
    | start =>
      cases heqΓ
      cases Γ' with
      | empty =>
        apply And.left ihA
        repeat' rfl
      | extend Γ' S' =>
        rw [←empty_expand_context (Γ := Γ' ⬝ S')]
        apply And.right (And.right ihA)
        repeat' rfl
    | expand Δ' S' =>
      cases heqΓ
      cases Γ with
      | empty =>
        rw [←empty_expand_context (Γ := ε)]
        apply ihiC
        rotate_left
        · apply n
        · apply Δ'
        · rfl
        · rfl
      | extend Γ' S' =>
        rw [←empty_expand_context (Γ := Γ' ⬝ S')]
        apply ihiC
        rotate_left
        · apply n
        · apply Δ'
        · rfl
        · rfl
