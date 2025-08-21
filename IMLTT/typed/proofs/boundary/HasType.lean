import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.RulesEquality
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

import IMLTT.typed.proofs.boundary.Helpers

theorem boundary_var :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x},
    Γ ⊢ A type
    → Γ ⊢ A type
    → Γ ⬝ A ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n Γ A hA _ihA
    apply weakening_type hA hA

theorem boundary_weak :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ∶ A)
    → Γ ⊢ B type
    → Γ ⊢ A type
    → Γ ⊢ B type
    → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n x Γ A B hvA hB ihvA ihB
    apply weakening_type
    · apply ihvA
    · apply ihB

theorem boundary_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → Γ ⊢ 𝟙 type :=
  by
    intro n Γ hiC ihiC
    apply IsType.unit_form hiC

theorem boundary_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)},
    (Γ ⬝ A ⊢ b ∶ B)
    → Γ ⬝ A ⊢ B type
    → Γ ⊢ ΠA;B type :=
  by
    intro n Γ A b B _hbB ihbB
    apply IsType.pi_form
    · have hiCA := boundary_ctx_type ihbB
      apply ctx_extr hiCA
    · apply ihbB

theorem boundary_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ∶ A)
    → (Γ ⊢ b ∶ B⌈a⌉₀)
    → Γ ⬝ A ⊢ B type
    → Γ ⊢ A type
    → Γ ⊢ B⌈a⌉₀ type
    → Γ ⬝ A ⊢ B type
    → Γ ⊢ ΣA;B type :=
  by
    intro n Γ a A b B haA hbB hB ihaA ihbB ihB
    apply IsType.sigma_form
    · apply ihaA
    · apply hB

theorem boundary_nat_zero_intro :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → Γ ⊢ 𝒩 type :=
  by
    intro n Γ hiC ihiC
    apply IsType.nat_form hiC

theorem boundary_nat_succ_intro :
    ∀ {n : Nat} {Γ : Ctx n} {x : Tm n},
    (Γ ⊢ x ∶ 𝒩)
    → Γ ⊢ 𝒩 type
    → Γ ⊢ 𝒩 type :=
  by
    intro n Γ x hxNat ihxNat
    apply ihxNat

theorem boundary_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n},
    Γ ⊢ A type
    → (Γ ⊢ a ∶ A)
    → Γ ⊢ A type
    → Γ ⊢ A type
    → Γ ⊢ a ≃[A] a type :=
  by
    intro n Γ A a hA haA ihA ihaA
    apply IsType.iden_form
    · apply hA
    · apply haA
    · apply haA

theorem boundary_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    apply IsType.univ_form hiC

theorem boundary_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC hiC
    apply IsType.univ_form hiC

theorem boundary_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ∶ 𝒰)
    → Γ ⊢ 𝒰 type
    → Γ ⬝ A ⊢ 𝒰 type
    → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A B hAU hBU ihAU ihBU
    apply ihAU

theorem boundary_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⬝ A ⊢ B ∶ 𝒰)
    → Γ ⊢ 𝒰 type
    → Γ ⬝ A ⊢ 𝒰 type
    → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A B hAU hBU ihAU ihBU
    apply ihAU

theorem boundary_univ_nat :
    ∀ {n : Nat} {Γ : Ctx n},
    Γ ctx
    → Γ ctx
    → Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    apply IsType.univ_form hiC

theorem boundary_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ A ∶ 𝒰)
    → (Γ ⊢ a ∶ A)
    → (Γ ⊢ a' ∶ A)
    → Γ ⊢ 𝒰 type
    → Γ ⊢ A type
    → Γ ⊢ A type
    → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A a a' hAU haA haA' ihAU ihaA ihaA'
    apply ihAU

theorem boundary_unit_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type
    → (Γ ⊢ a ∶ A⌈⋆⌉₀)
    → (Γ ⊢ b ∶ 𝟙)
    → Γ ⬝ 𝟙 ⊢ A type
    → Γ ⊢ A⌈⋆⌉₀ type
    → Γ ⊢ 𝟙 type
    → Γ ⊢ A⌈b⌉₀ type :=
  by
    intro n Γ A a b hA haA hb1 ihA ihaA ihb1
    apply substitution_type
    · apply hA
    · apply hb1

theorem boundary_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
    Γ ⬝ 𝟘 ⊢ A type
    → (Γ ⊢ b ∶ 𝟘)
    → Γ ⬝ 𝟘 ⊢ A type
    → Γ ⊢ 𝟘 type
    → Γ ⊢ A⌈b⌉₀ type :=
  by
    intro n Γ A b hA hb0 ihA ihb0
    apply substitution_type
    · apply hA
    · apply hb0

theorem boundary_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
    (Γ ⊢ f ∶ ΠA;B)
    → (Γ ⊢ a ∶ A)
    → Γ ⊢ ΠA;B type
    → Γ ⊢ A type
    → Γ ⊢ B⌈a⌉₀ type :=
  by
    intro n Γ f A B a hfPi haA ihfPi ihaA
    apply substitution_type
    · apply And.right (pi_is_type_inversion ihfPi)
    · apply haA

theorem boundary_sigma_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
  (Γ ⬝ ΣA;B) ⊢ C type →
    (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉) →
      (Γ ⊢ p ∶ ΣA;B) → (Γ ⬝ ΣA;B) ⊢ C type → Γ ⬝ A ⬝ B ⊢ C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉ type → Γ ⊢ ΣA;B type → Γ ⊢ C⌈p⌉₀ type :=
  by
    intro n Γ A B p C c hC hcC hpSi ihC ihcC ihpSi
    apply substitution_type
    · apply ihC
    · apply hpSi

theorem boundary_nat_elim :
    ∀ {n : Nat} {Γ : Ctx n} {z x : Tm n} {A : Tm (n + 1)} {s : Tm (n + 2)},
    Γ ⬝ 𝒩 ⊢ A type
    → (Γ ⊢ z ∶ A⌈𝓏⌉₀)
    → (Γ ⬝ 𝒩 ⬝ A ⊢ s ∶ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
    → (Γ ⊢ x ∶ 𝒩)
    → Γ ⬝ 𝒩 ⊢ A type
    → Γ ⊢ A⌈𝓏⌉₀ type
    → Γ ⬝ 𝒩 ⬝ A ⊢ A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋ type
    → Γ ⊢ 𝒩 type
    → Γ ⊢ A⌈x⌉₀ type :=
  by
    intro n Γ z x A s hA izA isA hxNat ihA ihzA ihsA ihxNat
    apply substitution_type
    · apply hA
    · apply hxNat

theorem boundary_iden_elim :
  ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b : Tm (n + 1)} {a a' p : Tm n},
  (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type
  → (Γ ⬝ A ⊢ b ∶ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉)
  → (Γ ⊢ a ∶ A)
  → (Γ ⊢ a' ∶ A)
  → (Γ ⊢ p ∶ a ≃[A] a')
  → (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))) ⊢ B type
  → Γ ⬝ A ⊢ B⌈(ₛidₚ)⋄ v(0)⋄ (A⌊↑ₚidₚ⌋.refl v(0))⌉ type
  → Γ ⊢ A type
  → Γ ⊢ A type
  → Γ ⊢ a ≃[A] a' type
  → Γ ⊢ B⌈(ₛidₚ)⋄ a⋄ a'⋄ p⌉ type :=
  by
    intro n Γ A B b a a' p hB hbB haA haA' hpId ihB ihbB ihaA ihaA' ihpId
    rw [context_to_gen_ctx] at hB
    rw [←middle_expand_context (Γ := Γ ⬝ A)] at hB
    have h1 := substitution_general_type hB haA
    simp only [substitute_into_gen_ctx] at h1
    rw [middle_expand_context] at h1
    have h2 : Γ ⊗ ⌈a'⌉(.start ⊙ (v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0))⌈a/ₙ(by omega)⌉ w/ (by omega))
              ⊢ B⌈a/ₙ(by omega)⌉⌈a'/ₙ(by omega)⌉ type :=
      by
        apply substitution_general_type
        · apply_subst_eq h1
        · apply_subst_eq haA'
    simp only [substitute_into_gen_ctx] at h2
    have h3 : Γ ⊢ B⌈a/ₙ(by omega)⌉⌈a'/ₙ(by omega)⌉⌈p⌉₀ type :=
      by
        apply substitution_type
        rotate_left
        · apply hpId
        · apply_subst_eq h2
    apply_subst_eq h3

theorem boundary_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n},
    (Γ ⊢ a ∶ A)
    → Γ ⊢ A ≡ B type
    → Γ ⊢ A type
    → Γ ⊢ A type ∧ Γ ⊢ B type
    → Γ ⊢ B type :=
  by
    intro n Γ a A B haA hAB ihaA ihAB
    apply And.right ihAB
