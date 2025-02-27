import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.admissable.Substitution
import IMLTT.typed.proofs.admissable.Inversion
import IMLTT.typed.proofs.boundary.BoundaryIsCtx

theorem boundary_var :
    ∀ {x : Nat} {Γ : Ctx x} {A : Tm x}, Γ ⊢ A type → Γ ⊢ A type → Γ ⬝ A ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n Γ A hA _ihA
    apply weakening_type hA hA

theorem boundary_weak :
    ∀ {x : Nat} {i : Fin x} {Γ : Ctx x} {A B : Tm x},
    (Γ ⊢ v(i) ∶ A) → Γ ⊢ B type → Γ ⊢ A type → Γ ⊢ B type → Γ ⬝ B ⊢ A⌊↑ₚidₚ⌋ type :=
  by
    intro n x Γ A B hvA hB ihvA ihB
    apply weakening_type
    · apply ihvA
    · apply ihB

theorem boundary_unit_intro :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ 𝟙 type :=
  by
    intro n Γ hiC ihiC
    apply IsType.unit_form hiC

theorem boundary_pi_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {b B : Tm (n + 1)}, (Γ ⬝ A ⊢ b ∶ B) → Γ ⬝ A ⊢ B type → Γ ⊢ ΠA;B type :=
  by
    intro n Γ A b B _hbB ihbB
    apply IsType.pi_form
    · have hiCA := boundary_ctx_type ihbB
      apply ctx_extr hiCA
    · apply ihbB

theorem boundary_sigma_intro :
    ∀ {n : Nat} {Γ : Ctx n} {a A b : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ a ∶ A) → (Γ ⊢ b ∶ B⌈a⌉₀) → Γ ⊢ A type → Γ ⊢ B⌈a⌉₀ type → Γ ⊢ ΣA;B type :=
  by
    intro n Γ a A b B haA _hbB ihaA ihbB
    apply IsType.sigma_form
    · apply ihaA
    · sorry
      -- apply substitution_inv_type
      -- · rfl
      -- · apply ihbB
      -- · apply haA

theorem boundary_iden_intro :
    ∀ {n : Nat} {Γ : Ctx n} {A a : Tm n}, Γ ⊢ A type → (Γ ⊢ a ∶ A) → Γ ⊢ A type → Γ ⊢ A type → Γ ⊢ a ≃[A] a type :=
  by
    intro n Γ A a hA haA ihA ihaA
    apply IsType.iden_form
    · apply hA
    · apply haA
    · apply haA

theorem boundary_univ_unit :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC ihiC
    apply IsType.univ_form hiC

theorem boundary_univ_empty :
    ∀ {n : Nat} {Γ : Ctx n}, Γ ctx → Γ ctx → Γ ⊢ 𝒰 type :=
  by
    intro n Γ hiC hiC
    apply IsType.univ_form hiC

theorem boundary_univ_pi :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) → (Γ ⬝ A ⊢ B ∶ 𝒰) → Γ ⊢ 𝒰 type → Γ ⬝ A ⊢ 𝒰 type → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A B hAU hBU ihAU ihBU
    apply ihAU

theorem boundary_univ_sigma :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)},
    (Γ ⊢ A ∶ 𝒰) → (Γ ⬝ A ⊢ B ∶ 𝒰) → Γ ⊢ 𝒰 type → Γ ⬝ A ⊢ 𝒰 type → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A B hAU hBU ihAU ihBU
    apply ihAU

theorem boundary_univ_iden :
    ∀ {n : Nat} {Γ : Ctx n} {A a a' : Tm n},
    (Γ ⊢ A ∶ 𝒰) → (Γ ⊢ a ∶ A) → (Γ ⊢ a' ∶ A) → Γ ⊢ 𝒰 type → Γ ⊢ A type → Γ ⊢ A type → Γ ⊢ 𝒰 type :=
  by
    intro n Γ A a a' hAU haA haA' ihAU ihaA ihaA'
    apply ihAU

theorem boundary_unit_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {a b : Tm n},
    Γ ⬝ 𝟙 ⊢ A type → (Γ ⊢ a ∶ A⌈⋆⌉₀) → (Γ ⊢ b ∶ 𝟙) → Γ ⬝ 𝟙 ⊢ A type → Γ ⊢ A⌈⋆⌉₀ type → Γ ⊢ 𝟙 type → Γ ⊢ A⌈b⌉₀ type :=
  by
    intro n Γ A a b hA haA hb1 ihA ihaA ihb1
    apply substitution_type
    · apply hb1
    · apply hA

theorem boundary_empty_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm (n + 1)} {b : Tm n},
    Γ ⬝ 𝟘 ⊢ A type → (Γ ⊢ b ∶ 𝟘) → Γ ⬝ 𝟘 ⊢ A type → Γ ⊢ 𝟘 type → Γ ⊢ A⌈b⌉₀ type :=
  by
    intro n Γ A b hA hb0 ihA ihb0
    apply substitution_type
    · apply hb0
    · apply hA

theorem boundary_pi_elim :
    ∀ {n : Nat} {Γ : Ctx n} {f A : Tm n} {B : Tm (n + 1)} {a : Tm n},
    (Γ ⊢ f ∶ ΠA;B) → (Γ ⊢ a ∶ A) → Γ ⊢ ΠA;B type → Γ ⊢ A type → Γ ⊢ B⌈a⌉₀ type :=
  by
    intro n Γ f A B a hfPi haA ihfPi ihaA
    apply substitution_type
    · apply haA
    · apply And.right (pi_is_type_inversion ihfPi)

theorem boundary_sigma_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1)} {p : Tm n} {C : Tm (n + 1)} {c : Tm (n + 1 + 1)},
    (Γ ⊢ p ∶ ΣA;B) →
    (Γ ⬝ ΣA;B) ⊢ C type →
    (Γ ⬝ A ⬝ B ⊢ c ∶ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) →
    Γ ⊢ ΣA;B type → (Γ ⬝ ΣA;B) ⊢ C type → Γ ⬝ A ⬝ B ⊢ C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉ type → Γ ⊢ C⌈p⌉₀ type :=
  by
    intro n Γ A B p C c hpSi hC hcC ihpSi ihC ihcC
    apply substitution_type
    · apply hpSi
    · apply ihC


theorem substitution_separate_degeneralized : -- TODO: is this provable?
    A⌈(ₛidₚ), s1, s2, s3⌉ = A⌈s3⌊↑ₚ↑ₚidₚ⌋⌉₀⌈s2⌊↑ₚidₚ⌋⌉₀⌈s1⌉₀ :=
  by
    simp [substitute_zero]
    simp [substitution_comp]
    simp [comp_substitute_substitute]
    simp [comp_substitute_weaken]
    simp [comp_substitute_substitute]
    sorry

theorem boundary_iden_elim :
    ∀ {n : Nat} {Γ : Ctx n} {A : Tm n} {B : Tm (n + 1 + 1 + 1)} {b a a' p : Tm n},
    (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
      (Γ ⊢ b ∶ B⌈(ₛidₚ), a, a, A.refl a⌉) →
        (Γ ⊢ p ∶ a ≃[A] a') →
          Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type →
            (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) ⊢ B type →
              Γ ⊢ B⌈(ₛidₚ), a, a, A.refl a⌉ type →
                Γ ⊢ a ≃[A] a' type → Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type → Γ ⊢ B⌈(ₛidₚ), a, a', p⌉ type :=
  by
    intro n Γ A B b a a' p hB hbB hpId hB' ihB ihbB ihpId ihB'
    -- rw [substitution_separate_degeneralized]
    -- have IdInv := iden_is_type_inversion ihpId
    -- apply substitution_type
    -- · apply And.left (And.right IdInv)
    -- · apply substitution_type
    --   · apply weakening_term
    --     · apply And.right (And.right IdInv)
    --     · apply And.left IdInv
    --   · apply substitution_type
    --     rw (config := {occs := .pos [2]}) [←weakening_shift_id]
    --     · apply weakening_term
    --       · apply weakening_term
    --         · apply hpId
    --         · apply And.left IdInv
    --       · apply weakening_type
    --         · apply And.left IdInv
    --         · apply And.left IdInv
    --     · apply hB
    apply ihB'

theorem boundary_ty_conv :
    ∀ {n : Nat} {Γ : Ctx n} {a A B : Tm n}, (Γ ⊢ a ∶ A) → Γ ⊢ A ≡ B type → Γ ⊢ A type → Γ ⊢ A type ∧ Γ ⊢ B type → Γ ⊢ B type :=
  by
    intro n Γ a A B haA hAB ihaA ihAB
    apply And.right ihAB
