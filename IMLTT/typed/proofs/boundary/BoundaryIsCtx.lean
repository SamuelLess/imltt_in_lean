import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.typed.JudgmentsAndRules

import IMLTT.typed.proofs.Recursor

import Aesop

/- # helper -/

theorem ctx_decr :
    Γ ⬝ A ctx → Γ ctx :=
  by
    intro hiCA
    match hiCA with
    | .extend hiC _ => apply hiC

theorem ctx_decr_eq :
    Γ ⬝ A = Γ' ⬝ A' ↔ Γ = Γ' ∧ A = A' :=
  by
    apply Iff.intro
    · intro hiCeq
      cases hiCeq with
      | refl =>
        apply And.intro
        · rfl
        · rfl
    · intro h
      simp [h]

theorem ctx_extr :
    Γ ⬝ A ctx → Γ ⊢ A type :=
  by
    intro hiCA
    match hiCA with
    | .extend _ hA => apply hA

/- # Γ ⊢ J → Γ ctx -/

theorem boundary_ctx :
  (∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A : Tm n}, Γ ⊢ A type → Γ ctx) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, (Γ ⊢ a ∶ A) → Γ ctx) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n}, Γ ⊢ A ≡ A' type → Γ ctx) ∧
  (∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n}, (Γ ⊢ a ≡ a' ∶ A) → Γ ctx)
 :=
  by
    apply judgment_recursor
      (motive_1 := fun Γ _hiC => Γ ctx)
      (motive_2 := fun Γ _A _hA => Γ ctx)
      (motive_3 := fun Γ _a _A _haA => Γ ctx)
      (motive_4 := fun Γ _A _A' _hAA => Γ ctx)
      (motive_5 := fun Γ _a _a' _A _haaA => Γ ctx)
    case HasTypePiIntro =>
      intro n Γ A b B _ hiCA
      apply ctx_decr hiCA
    case IsEqualTermPiIntroEq =>
      intro n Γ A b b' B _ _ _ hiCA _
      apply ctx_decr hiCA
    all_goals aesop

theorem boundary_ctx_type : ∀ {n : Nat} {Γ : Ctx n} {A : Tm n},
    Γ ⊢ A type → Γ ctx :=
  by
    intro n Γ A
    apply (And.left (And.right boundary_ctx))

theorem boundary_ctx_term : ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
    (Γ ⊢ a ∶ A) → Γ ctx :=
  by
    intro n Γ A a
    apply (And.left (And.right (And.right boundary_ctx)))

theorem boundary_ctx_type_eq : ∀ {n : Nat} {Γ : Ctx n} {A A' : Tm n},
    Γ ⊢ A ≡ A' type → Γ ctx :=
  by
    intro n Γ A A'
    apply (And.left (And.right (And.right (And.right boundary_ctx))))

theorem boundary_ctx_term_eq : ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ a ≡ a' ∶ A) → Γ ctx :=
  by
    intro n Γ A a a'
    apply (And.right (And.right (And.right (And.right boundary_ctx))))
