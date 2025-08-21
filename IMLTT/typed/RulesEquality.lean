import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Mixture

import IMLTT.untyped.Macros

import IMLTT.typed.JudgmentsAndRules

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

theorem replaceWithEq {goal repl : Prop} (eq : repl = goal) (prf : repl) :
    goal := by cases eq; refine prf

elab "apply_replace_meta" tm:term : tactic =>
  withMainContext do
    -- to @tm (make implicit parameters explicit)
    let atTm ← elabTermForApply tm
    let inferredType ← inferType atTm
    -- cut out and use only conclusion, replace quantified parameters with metavars
    -- ∀α β f, f α → f β to ?f ?β
    let (_, _, resultType) ← forallMetaTelescope inferredType
    liftMetaTactic fun goal => MVarId.apply goal resultType

elab "apply_to_prf" tm:term : tactic =>
  withMainContext do
    let goals ← getGoals
    for goal in goals do
      let tag ← goal.getTag
      if tag.toString.endsWith "prf" then
        let t ← goal.getType
        logInfo m!"found {t}"
        let atTm ← elabTermForApply tm
        liftMetaTactic fun _ => goal.apply atTm -- not sound
        return

-- colGt only reads to real line break (exluding indented)
macro "apply_subst_eq" colGt tm:term : tactic =>
  `(tactic|
    (
      apply replaceWithEq
      rotate_right
      apply_replace_meta $tm
      rotate_right; rotate_right
      congr 1 -- Γ ⊢ A type = Γ' ⊢ A' type to Γ = Γ' and A = A'
      try any_goals solve | substitution_norm_meta
      try any_goals solve | substitution_norm
      -- apply_to_prf $tm
      try any_goals apply $tm
    )
  )





-- deprecated

theorem useVarwithWeak :
    Γ ⊢ A type → A⌊↑ₚidₚ⌋ = B → Γ ⬝ A ⊢ v(0) ∶ B :=
  by
    intro hA hEq
    cases hEq
    apply HasType.var
    apply hA

theorem useWeakwithWeak :
    (Γ ⊢ v(i) ∶ A) → Γ ⊢ B type → v(i)⌊↑ₚidₚ⌋ = v(j) → A⌊↑ₚidₚ⌋ = A' → Γ ⬝ B ⊢ v(j) ∶ A' :=
  by
    intro hvA hB hEqv heqA
    cases hEqv
    cases heqA
    rw [←weaken]
    apply HasType.weak
    · apply hvA
    · apply hB

theorem use_equality_ctx {n : Nat} {Γ Δ : Ctx n}
    (hiC : Δ ctx) (heqΓ : Γ = Δ) :
    Γ ctx :=
  by
    simp_all

theorem use_equality_type {n : Nat} {Γ Δ : Ctx n} {A B : Tm n}
    (hB : Δ ⊢ B type) (heqΓ : Γ = Δ) (heqB : A = B) :
    Γ ⊢ A type :=
  by
    simp_all

theorem use_equality_term {n : Nat} {Γ Δ : Ctx n} {A B a b : Tm n}
    (hbB : Δ ⊢ b ∶ B) (heqΓ : Γ = Δ) (heqa : a = b) (heqA : A = B) :
    Γ ⊢ a ∶ A :=
  by
    simp_all

theorem use_equality_type_eq {n : Nat} {Γ Δ : Ctx n} {A B A' B' : Tm n}
    (hBB : Δ ⊢ B ≡ B' type) (heqΓ : Γ = Δ) (heqA : A = B) (heqA' : A' = B')
    : Γ ⊢ A ≡ A' type :=
  by
    simp_all

theorem use_equality_term_eq {n : Nat} {Γ Δ : Ctx n} {A B a b a' b' : Tm n}
    (hBB : Δ ⊢ b ≡ b' ∶ B) (heqΓ : Γ = Δ) (heqa : a = b) (heqa' : a' = b') (heqA : A = B)
    : Γ ⊢ a ≡ a' ∶ A :=
  by
    simp_all
