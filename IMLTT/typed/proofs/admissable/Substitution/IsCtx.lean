import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Contexts

import IMLTT.typed.JudgmentsAndRules

theorem substititution_gen_ctx_empty (m l : Nat) (Γ : Ctx l) (Δ : CtxGen (l + 1) (m + 1))
    (eqM : 0 = m + 1) (s S : Tm l) :
    eqM ▸ ε = Γ ⬝ S ⊗ Δ
    → (Γ ⊢ s ∶ S)
    → (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ctx :=
  by omega

theorem substitution_gen_extend :
  ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
  Γ ctx
  → Γ ⊢ A type
  → (∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) (s S : Tm l),
    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → (Γ_1 ⊢ s ∶ S)
    → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx)
  → (∀ (m l : Nat) {leq : l ≤ m} (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x = m + 1) {s S : Tm l}
      (A_1 : Tm (m + 1 - 1 + 1)),
    eqM ▸ Γ = Γ_1 ⬝ S ⊗ Δ
    → eqM ▸ A = A_1
    → (Γ_1 ⊢ s ∶ S)
    → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ⊢ A_1⌈s/ₙleq⌉ type)
  → ∀ (m l : Nat) (Γ_1 : Ctx l) (Δ : CtxGen (l + 1) (m + 1)) (eqM : x + 1 = m + 1) (s S : Tm l),
  eqM ▸ Γ ⬝ A = Γ_1 ⬝ S ⊗ Δ
  → (Γ_1 ⊢ s ∶ S)
  → Γ_1 ⊗ ⌈s⌉(Δ w/Nat.le_refl l) ctx :=
  by
    intro n Γ' A hiC hA ihiC ihA m l Γ Δ heqM s S heqΓ hsS
    cases heqM
    cases Δ
    case refl.start =>
      cases heqΓ
      simp []
      exact hiC
    case refl.expand Δ' T =>
      cases heqΓ
      cases n with
      | zero =>
        have h1 := gen_ctx_leq Δ'
        omega
      | succ n' =>
        simp [substitute_into_gen_ctx]
        apply IsCtx.extend
        · apply ihiC
          · rfl
          · apply hsS
          · rfl
        · apply ihA
          · rfl
          · rfl
          · apply hsS
          · rfl
