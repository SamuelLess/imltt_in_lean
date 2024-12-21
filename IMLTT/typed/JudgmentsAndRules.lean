import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Substitution
import IMLTT.untyped.Weakening

import aesop

/- # Rules -/
-- 5 judgments:
-- - Γ ctx
-- - Γ ⊢ A type
-- - Γ ⊢ a : A
-- - Γ ⊢ A = A' type
-- - Γ ⊢ a = a' : A

mutual
  -- Γ ctx
  @[aesop unsafe [constructors]]
  inductive IsCtx : Ctx n → Prop where
    | empty : IsCtx ε
    | extend : IsCtx Γ → IsType Γ A → IsCtx (Γ ⬝ A)

  -- Γ ⊢ A type
  @[aesop unsafe [constructors]]
  inductive IsType : Ctx n → Tm n → Prop where
    -- formation rules
    | unit_form :
      IsCtx Γ
      → IsType Γ 𝟙
    | empty_form :
      IsCtx Γ
      → IsType Γ 𝟘
    | pi_form :
      IsType Γ A → IsType (Γ ⬝ A) B
      → IsType Γ (ΠA;B)
    | sigma_form :
      IsType Γ A → IsType (Γ ⬝ A) B
      → IsType Γ (ΣA;B)
    | iden_form :
      HasType Γ a A → HasType Γ a' A
      → IsType Γ (a ≃[A] a')
    | univ_form :
      IsCtx Γ
      → IsType Γ 𝒰
    | univ_elim :
      HasType Γ A 𝒰
      → IsType Γ A

  -- Γ ⊢ a : A
  @[aesop unsafe [constructors]]
  inductive HasType : Ctx n → Tm n → Tm n → Prop where
    -- structural rules
    -- make sure variables of A refer to to same variables of Γ as before with lifting
    | var :
      IsType Γ A
      → HasType (Γ ⬝ A) v(0) (A⌊↑ₚidₚ⌋)
    -- | weak : HasType Γ (.var i) A → IsType Γ B
    --          → HasType (Γ ⬝ B) (.var (.succ i)) (weaken A (.shift .id))
    -- intro rules
    | unit_intro :
      IsCtx Γ
      → HasType Γ ⋆ 𝟙
    | pi_intro :
      HasType (Γ ⬝ A) b B
      → HasType Γ (λA;b) (ΠA;B)
    | sigma_intro :
      HasType Γ a A → HasType Γ b (B⌈a⌉₁)
      → HasType Γ (a&b) (ΣA;B)
    | iden_intro :
      HasType Γ a A
      → HasType Γ (A.refl a) (a ≃[A] a)
    -- universe intro
    | univ_unit :
      IsCtx Γ
      → HasType Γ 𝟙 𝒰
    | univ_empty :
      IsCtx Γ
      → HasType Γ 𝟘 𝒰
    | univ_pi : 
      HasType Γ A 𝒰 → HasType (Γ ⬝ A) B 𝒰
      → HasType Γ (ΠA;B) 𝒰
    | univ_sigma :
      HasType Γ A 𝒰 → HasType (Γ ⬝ A) B 𝒰
      → HasType Γ (ΣA;B) 𝒰
    | univ_iden : 
      HasType Γ A 𝒰 → HasType Γ a A → HasType Γ a' A
      → HasType Γ (a ≃[A] a') 𝒰
    -- elimination rules (except univ)
    | unit_elim :
      IsType (Γ ⬝ 𝟙) A → HasType Γ a (A⌈⋆⌉₁) → HasType Γ b 𝟙
      → HasType Γ (.indUnit A b a) (A⌈b⌉₁)
    | empty_elim :
      IsType (Γ ⬝ 𝟘) A → HasType Γ b 𝟘
      → HasType Γ (.indEmpty A b) (A⌈b⌉₁)
    | pi_elim :
      HasType Γ f (ΠA;B) → HasType Γ a A
      → HasType Γ (f◃a) (B⌈a⌉₁)
    | sigma_elim :
      HasType Γ p (ΣA;B) → IsType (Γ ⬝ ΣA;B) C → HasType (Γ ⬝ A ⬝ B) c (C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉)
      → HasType Γ (.indSigma A B C c p) (C⌈p⌉₁)
    | iden_elim :
      IsType (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) B
      → HasType Γ b (B⌈(ₛidₚ), a, a, .refl A a⌉)
      → HasType Γ p (a ≃[A] a')
      → HasType Γ (.j A B b a a' p) (B⌈(ₛidₚ), a, a', p⌉)
      -- conversion
    | ty_conv : 
      HasType Γ a A → IsEqualType Γ A B
      → HasType Γ a B

  -- Γ ⊢ A ≡ B type
  @[aesop unsafe [constructors]]
  inductive IsEqualType : Ctx n → Tm n → Tm n → Prop where
    -- congruence rules (formation)
    | unit_form_eq :
      IsCtx Γ
      → IsEqualType Γ 𝟙 𝟙
    | empty_form_eq :
      IsCtx Γ
      → IsEqualType Γ 𝟘 𝟘
    | pi_form_eq :
      IsEqualType Γ A A' → IsEqualType (Γ ⬝ A) B B'
      → IsEqualType Γ (ΠA;B) (ΠA';B')
    | sigma_form_eq :
      IsEqualType Γ A A' → IsEqualType (Γ ⬝ A) B B'
      → IsEqualType Γ (ΣA;B) (ΣA';B')
    | iden_form_eq :
      IsEqualType Γ A A' → IsEqualTerm Γ a₁ a₂ A → IsEqualTerm Γ a₃ a₄ A'
      → IsEqualType Γ (a₁ ≃[A] a₃) (a₂ ≃[A'] a₄)
    | univ_form_eq :
      IsCtx Γ
      → IsEqualType Γ 𝒰 𝒰
    | univ_elim_eq :
      IsEqualTerm Γ A A' 𝒰
      → IsEqualType Γ A A'

  -- Γ ⊢ a ≡ b : A
  @[aesop unsafe [constructors]]
  inductive IsEqualTerm : Ctx n → Tm n → Tm n → Tm n → Prop where
    | var_eq :
      IsType Γ A
      → IsEqualTerm (Γ ⬝ A) v(0) v(0) (A⌊↑ₚidₚ⌋)
    -- computation rules
    | unit_comp :
      IsType (Γ ⬝ 𝟙) A → HasType Γ a (A⌈⋆⌉₁) 
      → IsEqualTerm Γ (.indUnit A ⋆ a) a (A⌈⋆⌉₁)
    | pi_comp : 
      HasType (Γ ⬝ A) b B → HasType Γ a A 
      → IsEqualTerm Γ ((λA; b)◃a) (b⌈a⌉₁) (B⌈a⌉₁)
    | sigma_comp : 
      HasType Γ a A → HasType Γ b (B⌈a⌉₁) → IsType (Γ ⬝ ΣA;B) C 
      → HasType (Γ ⬝ A ⬝ B) c (C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉) 
      → IsEqualTerm Γ (.indSigma A B C c (a&b)) (c⌈(ₛidₚ), a, b⌉) (C⌈a&b⌉₁)
    | iden_comp :
      IsType (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) B
      → HasType Γ b (B⌈(ₛidₚ), a, a, .refl A a⌉)
      → HasType Γ a A
      → IsEqualTerm Γ (.j A B b a a (.refl A a)) b (B⌈(ₛidₚ), a, a, .refl A a⌉)
    -- congruence rules (introduction and elimination)
    | unit_intro_eq :
      IsCtx Γ
      → IsEqualTerm Γ ⋆ ⋆ 𝟙
    | unit_elim_eq :
      IsEqualType (Γ ⬝ 𝟙) A A' → IsEqualTerm Γ a a' (A⌈⋆⌉₁) → IsEqualTerm Γ b b' 𝟙
      → IsEqualTerm Γ (.indUnit A b a) (.indUnit A' b' a') (A⌈b⌉₁)
    | empty_elim_eq :
      IsEqualType (Γ ⬝ 𝟘) A A' → IsEqualTerm Γ b b' 𝟘 
      → IsEqualTerm Γ (.indEmpty A b) (.indEmpty A' b') (A⌈b⌉₁)
    | pi_intro_eq : 
      IsEqualTerm (Γ ⬝ A) b b' B
      → IsEqualTerm Γ (λA; b) (λA'; b') (ΠA;B)
    | pi_elim_eq :
      IsEqualTerm Γ f f' (ΠA;B) → IsEqualTerm Γ a a' A
      → IsEqualTerm Γ (f◃a) (f'◃a') (B⌈a⌉₁)
    | sigma_intro_eq : 
      IsEqualTerm Γ a a' A → IsEqualTerm Γ b b' (B⌈a⌉₁)
      → IsEqualTerm Γ (a&b) (a'&b') (ΣA;B)
    | sigma_elim_eq : 
      IsEqualType Γ (ΣA;B) (ΣA';B') → IsEqualTerm Γ p p' (ΣA;B) → IsEqualType (Γ ⬝ ΣA;B) C C'
      → IsEqualTerm (Γ ⬝ A ⬝ B) c c' (C⌈(ₛ↑ₚ↑ₚidₚ), v(1)&v(0)⌉)
      → IsEqualTerm Γ (.indSigma A B C c p) (.indSigma A' B' C' c' p') (C⌈p⌉₁)
    | iden_intro_eq : 
      IsEqualType Γ A A' → IsEqualTerm Γ a a' A
      → IsEqualTerm Γ (.refl A a) (.refl A' a') (.iden A a a)
    | iden_elim_eq : 
      IsEqualType (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) B B'
      → IsEqualTerm Γ b b' (B⌈(ₛidₚ), a₁, a₁, .refl A a₁⌉)
      → IsEqualType Γ (a₁ ≃[A] a₃) (a₂ ≃[A'] a₄)
      → IsEqualTerm Γ p p' (a₁ ≃[A] a₃) 
      → IsEqualTerm Γ (.j A B b a₁ a₃ p) (.j A' B' b' a₂ a₄ p') (B⌈(ₛidₚ), a₁, a₃, p⌉)
    | univ_unit_eq :
      IsCtx Γ
      → IsEqualTerm Γ 𝟙 𝟙 𝒰
    | univ_empty_eq :
      IsCtx Γ
      → IsEqualTerm Γ 𝟘 𝟘 𝒰
    | univ_pi_eq : 
      IsEqualTerm Γ A A' 𝒰 → IsEqualTerm (Γ ⬝ A) B B' 𝒰
      → IsEqualTerm Γ (ΠA;B) (ΠA';B') 𝒰
    | univ_sigma_eq : 
      IsEqualTerm Γ A A' 𝒰 → IsEqualTerm (Γ ⬝ A) B B' 𝒰 
      → IsEqualTerm Γ (ΣA;B) (ΣA';B') 𝒰
    | univ_iden_eq :
      IsEqualTerm Γ A A' 𝒰 → IsEqualTerm Γ a₁ a₂ A → IsEqualTerm Γ a₃ a₄ A 
      → IsEqualTerm Γ (a₁ ≃[A] a₃) (a₂ ≃[A'] a₄) 𝒰
    -- conversion
    | ty_conv_eq : 
      IsEqualTerm Γ a b A → IsEqualType Γ A B
      → IsEqualTerm Γ a b B
end

postfix:90 " ctx" => IsCtx
notation:90 Γ " ⊢ " A  " type" => IsType Γ A
notation:90 Γ " ⊢ " s " ∶ " A => HasType Γ s A
notation:90 Γ " ⊢ " A " ≡ " B " type" => IsEqualType Γ A B
notation:90 Γ " ⊢ " s " ≡ " t " ∶ " A => IsEqualTerm Γ s t A
