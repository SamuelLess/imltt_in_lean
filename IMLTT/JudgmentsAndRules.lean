import IMLTT.AbstractSyntax
-- import IMLTT.Substitution
import IMLTT.SubstitutionSep

/- # Rules -/
-- 5 judgments:
-- - Γ ctx
-- - Γ ⊢ A type
-- - Γ ⊢ a : A
-- - Γ ⊢ A = A' type
-- - Γ ⊢ a = a' : A

mutual
  -- Γ ctx
  inductive IsCtx : Ctx → Prop where
    | empty : IsCtx Ctx.empty
    | extend : IsCtx Γ → IsType Γ A → IsCtx (Γ ⬝ A)

  -- Γ ⊢ A type
  inductive IsType : Ctx → Tm → Prop where
    -- formation rules
    | unit_form : IsCtx Γ
                  → IsType Γ 𝟙
    | empty_form : IsCtx Γ
                   → IsType Γ 𝟘
    | pi_form : IsType Γ A → IsType (Γ ⬝ A) B
                → IsType Γ (Tm.pi A B)
    | sigma_form : IsType Γ A → IsType (Γ ⬝ A) B
                   → IsType Γ (Tm.sigma A B)
    | iden_form : HasType Γ a A → HasType Γ a' A
                  → IsType Γ (Tm.iden A a a')
    | univ_form : IsCtx Γ
                  → IsType Γ U
    | univ_elim : HasType Γ A U
                  → IsType Γ A

  -- Γ ⊢ a : A
  inductive HasType : Ctx → Tm → Tm → Prop where
    -- structural rules
    -- make sure variables of A refer to to same variables of Γ as before with lifting
    | var  : IsType Γ A
             → HasType (Γ ⬝ A) 0 (shift_tm A)
    | weak : HasType Γ (Tm.var i) A → IsType Γ B
             → HasType (Γ ⬝ B) (Tm.var (i + 1)) (shift_tm A)
    -- intro rules
    | unit_intro : IsCtx Γ
                   → HasType Γ tt 𝟙
    | pi_intro : HasType (Γ ⬝ A) b B
                 → HasType Γ (Tm.lam A b) (Tm.pi A B)
    | sigma_intro : HasType Γ a A → HasType Γ b (substitute_zero B a)
                    → HasType Γ (Tm.pairSigma a b) (Tm.sigma A B)
    | iden_intro : HasType Γ a A
                   → HasType Γ (Tm.refl A a) (Tm.iden A a a)
    -- universe intro
    | univ_unit : IsCtx Γ
                  → HasType Γ 𝟙 U
    | univ_empty : IsCtx Γ
                   → HasType Γ 𝟘 U
    | univ_pi : HasType Γ A U → HasType (Γ ⬝ A) B U
                → HasType Γ (Tm.pi A B) U
    | univ_sigma : HasType Γ A U → HasType (Γ ⬝ A) B U
                   → HasType Γ (Tm.sigma A B) U
    | univ_iden : HasType Γ A U → HasType Γ a A → HasType Γ a' A
                  → HasType Γ (Tm.iden A a a') U
    -- elimination rules (except univ)
    | unit_elim : IsType (Γ ⬝ Tm.unit) C → HasType Γ c (substitute_zero C Tm.unit)
                  → HasType Γ p Tm.unit
                  → HasType Γ (Tm.indUnit C p c) (substitute_zero C p)
    | empty_elim : IsType (Γ ⬝ 𝟘) C → HasType Γ p 𝟘
                   → HasType Γ (Tm.indEmpty C p) (substitute_zero C p)
    | pi_elim : HasType Γ f (Tm.pi A B) → HasType Γ a A
                → HasType Γ (Tm.app f a) (substitute_zero B a)
    | sigma_elim : HasType Γ p (Tm.sigma A B) → IsType (Γ ⬝ (Tm.sigma A B)) C
                   → HasType (Γ ⬝ A ⬝ B) c (substitute_zero C (Tm.pairSigma 1 0))
                   → HasType Γ (Tm.indSigma A B C c p) (substitute_zero C p)
    | iden_elim : IsType (((Γ ⬝ A) ⬝ (shift_tm A)) ⬝ (Tm.iden A 1 0)) B
                  → HasType (Γ ⬝ A) b
                    (substitute (substitute (substitute B 0 2) 0 1) (Tm.refl A 0) 0)
                  → HasType Γ p (Tm.iden A a a')
                  → HasType Γ (Tm.j A B b a a' p)
                    (substitute (substitute (substitute B a 2) a' 1) p 0)

    -- conversion
    | ty_conv : HasType Γ a A → IsEqualType Γ A B
                → HasType Γ a B

  -- Γ ⊢ A ≡ B type
  inductive IsEqualType : Ctx → Tm → Tm → Prop where
    -- congruence rules (formation)
    | unit_form_eq : IsCtx Γ
                     → IsEqualType Γ Tm.unit Tm.unit
    | empty_form_eq : IsCtx Γ
                      → IsEqualType Γ Tm.empty Tm.empty
    | pi_form_eq : IsEqualType Γ A A' → IsEqualType (Γ ⬝ A) B B'
                   → IsEqualType Γ (Tm.pi A B) (Tm.pi A' B')
    | sigma_form_eq : IsEqualType Γ A A' → IsEqualType (Γ ⬝ A) B B'
                      → IsEqualType Γ (Tm.sigma A B) (Tm.sigma A' B')
    | iden_form_eq : IsEqualTerm Γ a a' A → IsEqualTerm Γ a'' a''' A
                     → IsEqualType Γ (Tm.iden A a a'') (Tm.iden A a' a''')
    | univ_form_eq : IsCtx Γ
                     → IsEqualType Γ Tm.univ Tm.univ
    | univ_elim_eq : IsEqualTerm Γ A A' Tm.univ → IsEqualType Γ A A'

  -- Γ ⊢ a ≡ b : A
  inductive IsEqualTerm : Ctx → Tm → Tm → Tm → Prop where
    | var_eq : IsType Γ A → IsEqualTerm (Γ ⬝ A) 0 0 (shift_tm A)
    -- computation rules
    | unit_comp : IsType (Γ ⬝ 𝟙) C → HasType Γ c (substitute_zero C Tm.tt)
                  → IsEqualTerm Γ (Tm.indUnit A Tm.tt c) Tm.tt (substitute_zero C Tm.tt)
    | pi_comp : HasType (Γ ⬝ A) b B → HasType Γ a A
                → IsEqualTerm Γ (Tm.app (Tm.lam A b) a) (substitute_zero b a) (substitute_zero B a)
    | sigma_comp : HasType Γ a A → HasType (Γ ⬝ A) b (substitute_zero B a)
                   → IsType (Γ ⬝ (Tm.sigma A B)) C
                   → HasType (Γ ⬝ A ⬝ B) c (substitute_zero C (Tm.pairSigma 1 0))
                   → IsEqualTerm Γ (Tm.indSigma A B C c (Tm.pairSigma a b))
                     (substitute (substitute c a 0) b 0) (substitute_zero C (Tm.pairSigma a b))
    | iden_comp : IsType (((Γ ⬝ A) ⬝ (shift_tm A)) ⬝ (Tm.iden A 1 0)) B
                  → HasType (Γ ⬝ A) b
                    (substitute (substitute (substitute B 0 2) 0 1) (Tm.refl A 0) 0)
                  → HasType Γ a A
                  → IsEqualTerm Γ (Tm.j A B b a a' (Tm.refl A a)) (substitute b a 0)
                    (substitute (substitute (substitute B a 2) a' 1) (Tm.refl A a) 0)

    -- congruence rules (introduction and elimination)
    | unit_intro_eq : IsCtx Γ
                      → IsEqualTerm Γ Tm.tt Tm.tt Tm.unit
    | unit_elim_eq : IsEqualType (Γ ⬝ 𝟙) A A' → IsEqualTerm Γ a a' (substitute_zero A Tm.tt)
                     → IsEqualTerm Γ b b' Tm.unit
                     → IsEqualTerm Γ (Tm.indUnit A b a) (Tm.indUnit A' b' a') (substitute_zero A b)
    | empty_elim_eq : IsEqualType (Γ ⬝ Tm.empty) A A' → IsEqualTerm Γ b b' Tm.empty
                      → IsEqualTerm Γ (Tm.indEmpty A b) (Tm.indEmpty A' b') (substitute_zero A b)
    | pi_intro_eq : IsEqualType Γ A A' → IsEqualType (Γ ⬝ A) B B' → IsEqualTerm (Γ ⬝ A) b b' B
                    → IsEqualTerm Γ (Tm.lam A b) (Tm.lam A' b') (Tm.pi A B)
    | pi_elim_eq : IsEqualType Γ (Tm.pi A B) (Tm.pi A' B') → IsEqualTerm Γ a a' A
                   → IsEqualTerm Γ f f' (Tm.pi A B)
                   → IsEqualTerm Γ (Tm.app f a) (Tm.app f' a') (substitute_zero B a)
    | sigma_intro_eq : IsEqualType Γ A A' → IsEqualType (Γ ⬝ A) B B' → IsEqualTerm Γ a a' A
                       → IsEqualTerm (Γ ⬝ A) b b' (substitute_zero B a)
                       → IsEqualTerm Γ (Tm.pairSigma a b) (Tm.pairSigma a' b') (Tm.sigma A B)
    | sigma_elim_eq : IsEqualType Γ (Tm.sigma A B) (Tm.sigma A' B')
                      → IsEqualTerm Γ p p' (Tm.sigma A B) 
                      → IsEqualType (Γ ⬝ (Tm.sigma A B)) C C'
                      → IsEqualTerm (Γ ⬝ A ⬝ B) c c' (substitute_zero C (Tm.pairSigma 1 0))
                      → IsEqualTerm Γ (Tm.indSigma A B C c p) (Tm.indSigma A B C c' p') 
                        (substitute_zero C p)
    | iden_intro_eq : IsEqualTerm Γ a a' A
                      → IsEqualTerm Γ (Tm.refl A a) (Tm.refl A a') (Tm.iden A a a)
    | iden_elim_eq : IsEqualType (((Γ ⬝ A) ⬝ (shift_tm A)) ⬝ (Tm.iden A 1 0)) B B'
                     → IsEqualTerm (Γ ⬝ A) b b'
                       (substitute (substitute (substitute B 0 2) 0 1) (Tm.refl A 0) 0)
                     → IsEqualTerm Γ p p' (Tm.iden A a a')
                     → IsEqualTerm Γ (Tm.j A B b a a' p) (Tm.j A B b' a a' p')
                       (substitute (substitute (substitute B a 2) a' 1) p 0)

    -- conversion
    | ty_conv_eq : IsEqualTerm Γ a b A → IsEqualType Γ A B
                   → IsEqualTerm Γ a b B
end

postfix : max " ctx" => IsCtx
notation Γ " ⊢ " A  " type" => IsType Γ A
notation Γ " ⊢ " s " ∶ " A => HasType Γ s A
notation Γ " ⊢ " A " ≡ " B " type" => IsEqualType Γ A B
notation Γ " ⊢ " s " ≡ " t " ∶ " A => IsEqualTerm Γ s t A
