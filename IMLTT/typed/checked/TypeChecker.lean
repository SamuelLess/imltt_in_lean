import IMLTT.typed.JudgmentsAndRules
import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Elaboration
import IMLTT.typed.annotated.Substitution
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

--set_option profiler true
--set_option profiler.threshold 100 -- Optional: only show tactics that take longer than 100ms

def fuel := 200 -- proof go brrr 🚗

def is_ctx : ((k : Nat) → (Γsome : ACtx k) → (T : ATm k) →
    Except String (PLift (Γsome.toCtx ⊢ T.toTm type)))
    -> (Γ : ACtx n) -> Except String (PLift (Γ.toCtx ctx))
  | _, .empty => pure <| .up IsCtx.empty
  | my_is_type, ACtx.extend _ Γ' T' => do
    let ctx_ok ← is_ctx my_is_type Γ'
    let t_ok : PLift (Γ'.toCtx ⊢ T'.toTm type) ← my_is_type _ Γ' T'
    return .up <| IsCtx.extend ctx_ok.down t_ok.down

notation Γ "⬝a" A => ACtx.extend Lean.Name.anonymous Γ A

set_option maxHeartbeats 500000
mutual
  def is_type  (fuel : Nat)  (n : Nat)
       (Γ : ACtx n) (T : ATm n) : Except String (PLift (Γ.toCtx ⊢ T.toTm type)) :=
    match fuel, n, Γ, T with
    | 0, _, _, _ => .error "is_type: out of fuel"
    | f+1, _, Γ, .empty => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsType.empty_form ctx_ok.down
    | f+1, _, Γ, .unit => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsType.unit_form ctx_ok.down
    | f+1, _, Γ, .nat => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsType.nat_form ctx_ok.down
    | f+1, _, Γ, .univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsType.univ_form ctx_ok.down
    | f+1, _, Γ, .pi A B => do
      let is_type_A ← is_type f _ Γ A
      let is_type_B ← is_type f _ (Γ ⬝a A) B
      return .up <| IsType.pi_form is_type_A.down is_type_B.down
    | f+1, _, Γ, .sigma A B => do
      let is_type_A ← is_type f _ Γ A
      let is_type_B ← is_type f _ (Γ ⬝a A) B
      return .up <| IsType.sigma_form is_type_A.down is_type_B.down
    | f+1, _, Γ, .iden A a a' => do
      let is_type_A ← is_type f _ Γ A
      let has_type_a ← has_type f Γ a A
      let has_type_a' ← has_type f Γ a' A
      return .up <| IsType.iden_form is_type_A.down has_type_a.down has_type_a'.down
    | f+1, _, Γ, A => do
      let has_type_A ← has_type f Γ A .univ
      return .up <| IsType.univ_elim has_type_A.down
  termination_by structural fuel

  def has_type (fuel : Nat) (Γ : ACtx n)
      (t : ATm n) (T : ATm n) : Except String (PLift (Γ.toCtx ⊢ t.toTm ∶ T.toTm)) :=
    match fuel, Γ, t, T with
    | 0, _, _, _ => .error "has_type: out of fuel"
    -- variables
    | _+1, .empty, .var i, T => .error s!"has_type: can't have v({i}) in empty context"
    | f+1, ACtx.extend _ Γ T, .var ⟨0,_⟩, T' =>  do
      let is_type_T ← is_type f _ Γ T
      let is_eq_type_T_T' ← is_eq_type f (Γ ⬝a T) (T⌊ₐ↑ₚidₚ⌋) T'
      have has_type_T := HasType.var is_type_T.down
      return .up <| HasType.ty_conv has_type_T ((toTm_weak _ _) ▸ is_eq_type_T_T'.down)
    | f+1, ACtx.extend _ Γ T, .var ⟨i+1, hi⟩, T' => do
      let ⟨T'', h⟩ ← infer_type f Γ (.var ⟨i, (Nat.succ_lt_succ_iff.mp hi)⟩)
      let is_type_T ← is_type f _ Γ T
      let is_eq_type_T ← is_eq_type f (Γ ⬝a T) (T''⌊ₐ↑ₚidₚ⌋) T'
      let weak := HasType.weak h is_type_T.down
      return .up <| HasType.ty_conv weak ((toTm_weak _ _) ▸ is_eq_type_T.down)
    -- intro rules
    | f+1, Γ, .tt, Unit => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type ← is_eq_type f Γ .unit Unit
      return .up <| HasType.ty_conv (HasType.unit_intro ctx_ok.down) is_eq_type.down
    | f+1, Γ, .zeroNat, N => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type ← is_eq_type f Γ .nat N
      return .up <| HasType.ty_conv (HasType.nat_zero_intro ctx_ok.down) is_eq_type.down
    | f+1, Γ, .succNat n, N => do
      let has_type_n ← has_type f Γ n .nat
      let is_eq_type_N ← is_eq_type f Γ .nat N
      return .up <| HasType.ty_conv (HasType.nat_succ_intro has_type_n.down) is_eq_type_N.down
    | f+1, Γ, .lam A t, P => do
      let ⟨.pi A' B', hp⟩ ← infer_type f Γ (.lam A t)
        | .error s!"has_type: expected Π-type at {λA.toTm;t.toTm}, instead got {P.toTm}"
      let has_type_t ← has_type f (Γ ⬝a A) t B' -- v(0) is now bound by A
      let pi_intro := HasType.pi_intro has_type_t.down
      let is_eq_type_P ← is_eq_type f Γ (.pi A B') P
      return .up <| HasType.ty_conv pi_intro is_eq_type_P.down
    | f+1, Γ, .pairSigma a b B, S => do
      let ⟨A, ha⟩ ← infer_type f Γ a
      let hb ← has_type f Γ b (B⌈ₐa⌉₀)
      let hb_type ← is_type f _ (Γ ⬝a A) B
      let sig_intro := HasType.sigma_intro ha ((toTm_subst _ _) ▸ hb.down) hb_type.down
      let is_eq_type_S ← is_eq_type f Γ (.sigma A B) S
      return .up <| HasType.ty_conv sig_intro is_eq_type_S.down
    | f+1, Γ, ATm.refl A a, ATm.iden A' a' a'' => do
      let is_type_A ← is_type f _ Γ A
      let has_type_a ← has_type f Γ a A
      have t : Γ.toCtx ⊢ (A.refl a).toTm ∶  (A'.iden a' a'').toTm := by
        apply HasType.ty_conv (B:=(A'.iden a' a'').toTm)
        apply HasType.iden_intro is_type_A.down has_type_a.down
        apply IsEqualType.iden_form_eq
        · exact (← is_eq_type f Γ A A').down
        · exact (← is_eq_term f Γ a a' A).down
        · exact (← is_eq_term f Γ a a'' A').down
      return .up <| t
    -- univ intro rules
    | f+1, Γ, .empty, Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ .univ Univ
      return .up <| HasType.ty_conv (HasType.univ_empty ctx_ok.down) is_eq_type_U.down
    | f+1, Γ, .unit, Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ .univ Univ
      return .up <| HasType.ty_conv (HasType.univ_unit ctx_ok.down) is_eq_type_U.down
    | f+1, Γ, .nat, Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ .univ Univ
      return .up <| HasType.ty_conv (HasType.univ_nat ctx_ok.down) is_eq_type_U.down
    | f+1, Γ, .pi A B , Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ .univ Univ
      let has_type_A_U ← has_type f Γ A .univ
      let has_type_B_U ← has_type f (Γ ⬝a A) B .univ
      return .up <| HasType.ty_conv
        (HasType.univ_pi has_type_A_U.down has_type_B_U.down) is_eq_type_U.down
    | f+1, Γ, .sigma A B , Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ .univ Univ
      let has_type_A_U ← has_type f Γ A .univ
      let has_type_B_U ← has_type f (Γ ⬝a A) B .univ
      return .up <| HasType.ty_conv
        (HasType.univ_sigma has_type_A_U.down has_type_B_U.down) is_eq_type_U.down
    | f+1, Γ, .iden A a a' , Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ .univ Univ
      let has_type_A_U ← has_type f Γ A .univ
      let has_type_a_A ← has_type f Γ a A
      let has_type_a'_A ← has_type f Γ a' A
      return .up <| HasType.ty_conv
        (HasType.univ_iden has_type_A_U.down has_type_a_A.down has_type_a'_A.down) is_eq_type_U.down
    -- elim rules
    | f+1, Γ, .indEmpty A a, B => do
      return .up <| by
        apply HasType.ty_conv (B:=B.toTm)
        apply HasType.empty_elim
        · exact (← is_type f _ (Γ ⬝a .empty) A).down
        · exact (← has_type f Γ a .empty).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (A⌈ₐa⌉₀) B).down
    | f+1, Γ, .indUnit A b a, B => do
      return .up <| by
        apply HasType.ty_conv (B:=B.toTm)
        apply HasType.unit_elim
        · exact (← is_type f _ (Γ ⬝a .unit) A).down
        · let h := (← has_type f Γ a (A⌈ₐ.tt⌉₀)).down
          rewrite [toTm_subst] at h
          exact h
        · exact (← has_type f Γ b .unit).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (A⌈ₐb⌉₀) B).down
    | f+1, Γ, .app g a, B' => do
      let ⟨.pi A B, hg⟩ ← infer_type f Γ g
        | .error s!"has_type: expected lambda term at {g.toTm}"
      let has_type_a ← has_type f Γ a A
      have pi_elim := HasType.pi_elim hg has_type_a.down
      let is_eq_type_B ← is_eq_type f Γ (B⌈ₐa⌉₀) B'
      return .up <| HasType.ty_conv pi_elim <| (toTm_subst _ _) ▸ is_eq_type_B.down
    | f+1, Γ, .indSigma A B C c p, C' => do
      return .up <| by
        apply HasType.ty_conv (B:=C'.toTm)
        apply HasType.sigma_elim
        · exact (← is_type f _ (Γ ⬝a .sigma A B) C).down
        · let h := (← has_type f ((Γ ⬝a A) ⬝a B) c (C⌈ₐ(ₐₛ↑ₚ↑ₚidₚ)⋄ₐ (.pairSigma (.var 1) (.var 0) (B⌊ₐ↑ₚ↑ₚidₚ⌋))⌉)).down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          sorry -- FIXME: this will be fixed with the more general statement of toTm_subst
        · exact (← has_type f Γ p (.sigma A B)).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (C⌈ₐp⌉₀) C').down
    | f+1, Γ, .indNat A z s n, A' => do
      return .up <| by
        apply HasType.ty_conv (B:=A'.toTm)
        apply HasType.nat_elim
        · exact (← is_type f _ (Γ ⬝a .nat) A).down
        · let h := (← has_type f Γ z (A⌈ₐ .zeroNat⌉₀)).down
          rewrite [toTm_subst] at h
          exact h
        · let h := (← has_type f ((Γ ⬝a .nat) ⬝a A) s (A⌈ₐ(ₐₛ↑ₚidₚ)⋄ₐ (.succNat <| .var 0)⌉⌊ₐ↑ₚidₚ⌋)).down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          sorry -- FIXME: this will be fixed with the more general statement of toTm_subst
        · exact (← has_type f Γ n .nat).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (A⌈ₐn⌉₀) A').down
    | f+1, Γ, .j A B b a a' p, B' => do
      return .up <| by
        apply HasType.ty_conv (B:=B'.toTm)
        apply HasType.iden_elim
        · let h := (← is_type f _ (((Γ ⬝a A) ⬝a A⌊ₐ↑ₚidₚ⌋) ⬝a (.iden (A⌊ₐ↑ₚ↑ₚidₚ⌋) (.var 1) (.var 0))) B).down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_weak] at h
          simp [ATm.toTm] at h
          rewrite [toTm_weak] at h
          exact h
        · let h := (← has_type f (Γ ⬝a A) b (B⌈ₐ(ₐₛidₚ)⋄ₐ (.var 0)⋄ₐ .refl (A⌊ₐ↑ₚidₚ⌋) (.var 0)⌉)).down
          rewrite [toCtx_extend] at h
          sorry -- FIXME: this might be fixed with the more general statement of toTm_subst
        · exact (← has_type f Γ a A).down
        · exact (← has_type f Γ a' A).down
        · exact (← has_type f Γ p (.iden A a a')).down
        · let h := (← is_eq_type f Γ (B⌈ₐ(ₐₛidₚ)⋄ₐ a⋄ₐ a'⋄ₐ p⌉) B').down
          sorry -- FIXME: this will be fixed with the more general statement of toTm_subst
    | _, _, t, T => .error s!"has_type: unsupported pattern {t.toTm} ∶ {T.toTm}"
  termination_by structural fuel

  def is_eq_type (fuel : Nat) (Γ : ACtx n) (A : ATm n) (B : ATm n) :
      Except String (PLift (Γ.toCtx ⊢ A.toTm ≡ B.toTm type)) :=
    match fuel, Γ, A, B with
    | 0, _, A, B => .error s!"is_eq_type: out of fuel {A.toTm} ≡ {B.toTm}"
    -- congruence (formation) rules
    | f+1, Γ, .empty, .empty => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.empty_form_eq ctx_ok.down
    | f+1, Γ, .unit, .unit => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.unit_form_eq ctx_ok.down
    | f+1, Γ, .nat, .nat => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.nat_form_eq ctx_ok.down
    | f+1, Γ, .univ, .univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.univ_form_eq ctx_ok.down
    | f+1, Γ, .pi A B, .pi A' B' => do
      let eq_type_A ← is_eq_type f (Γ) A A'
      let eq_type_B ← is_eq_type f (Γ ⬝a A) B B'
      return .up <| IsEqualType.pi_form_eq eq_type_A.down eq_type_B.down
    | f+1, Γ, .sigma A B, .sigma A' B' => do
      let eq_type_A ← is_eq_type f (Γ) A A'
      let eq_type_B ← is_eq_type f (Γ ⬝a A) B B'
      return .up <| IsEqualType.sigma_form_eq eq_type_A.down eq_type_B.down
    | f+1, Γ, .iden A a₁ a₃, .iden A' a₂ a₄ => do
      let eq_type_A ← is_eq_type f Γ A A'
      let eq_term <- is_eq_term f Γ a₁ a₂ A
      let eq_term' <- is_eq_term f Γ a₃ a₄ A'
      return .up <| IsEqualType.iden_form_eq eq_type_A.down eq_term.down eq_term'.down
    -- TODO: check if more patterns are needed here
    | f+1, ACtx.extend _ Γ T, .var i, T' => do
      let ⟨.univ, _⟩ ← infer_type f (Γ ⬝a T) <| .var i
        | .error s!"is_eq_type: expected 𝒰 at v({i})"
      let eq_term_in_𝒰 ← is_eq_term f (Γ ⬝a T) (.var i) T' .univ
      return .up <| IsEqualType.univ_elim_eq eq_term_in_𝒰.down
    | f+1, Γ, .app g x, T => do
      let eq_term_in_𝒰 ← is_eq_term f Γ (.app g x) T .univ
      return .up <| IsEqualType.univ_elim_eq eq_term_in_𝒰.down
    | f+1, Γ, T, T' => do
      let is_eq_symm ← is_eq_type f Γ T' T
      return .up <| IsEqualType.type_symm is_eq_symm.down
  termination_by structural fuel

  def is_eq_term (fuel: Nat) (Γ : ACtx n)
      (a : ATm n) (a' : ATm n) (A : ATm n) : Except String (PLift (Γ.toCtx ⊢ a.toTm ≡ a'.toTm ∶ A.toTm)) :=
    match fuel, Γ, a, a', A with
    | 0, Γ, a, a', A =>
      .error s!"is_eq_term: out of fule with {repr Γ} ⊢ {a.toTm} ≡ {a'.toTm} : {A.toTm}"
    -- variables
    | f+1, Γ ⬝a T, .var 0, .var 0, T' => do
      let is_type_T ← is_type f _ Γ T
      let is_eq_T_T' ← is_eq_type f (Γ ⬝a T) (T⌊ₐ↑ₚidₚ⌋) T'
      have := IsEqualTerm.var_eq is_type_T.down
      return .up <| IsEqualTerm.ty_conv_eq this ((toTm_weak _ _) ▸ is_eq_T_T'.down)
    /-| f+1, Γ ⬝a T, .var ⟨i+1,hi⟩, .var ⟨j+1,hj⟩, T' => do
      if hieqj : i == j then
        let ⟨Tvi, htvi⟩ ← infer_type f Γ (.var (⟨i, (Nat.succ_lt_succ_iff.mp hi)⟩))
        have t : Γ ⬝ T ⊢ v(⟨i+1, hi⟩) ≡ v(⟨j+1, hj⟩) ∶ T' := by
          simp only [beq_iff_eq.mp hieqj |>.symm]
          rw [←Fin.succ_mk]
          apply IsEqualTerm.ty_conv_eq
          apply IsEqualTerm.weak_eq
          · exact defeq_refl_term htvi
          · exact (← is_type f _ Γ T).down
          · exact (← is_eq_type f (Γ ⬝ T) (Tvi⌊↑ₚidₚ⌋) T').down
        return .up t
      else
        .error s!"is_eq_term: two different variables cannot defeq v({i}) ≡ v({j}) ∶ {T'}"-/
    -- computation rules
    /-| f+1, Γ, .indUnit A ⋆ a, a', A' => do
      let is_type_A ← is_type f _ (Γ ⬝ 𝟙) A
      let has_type_a ← has_type f Γ a (A⌈⋆⌉₀)
      let is_eq_term_a_a' ← is_eq_term f Γ a a' (A⌈⋆⌉₀)
      let is_eq_type_A_A' ← is_eq_type f Γ (A⌈⋆⌉₀) A'
      have unit_comp := IsEqualTerm.unit_comp is_type_A.down has_type_a.down
      have term_trans := IsEqualTerm.term_trans unit_comp is_eq_term_a_a'.down
      return .up <| IsEqualTerm.ty_conv_eq term_trans is_eq_type_A_A'.down
    | f+1, Γ, (λA;b)◃x, t, T => do
      let ⟨Π_;B, _⟩ ← infer_type f Γ (λA;b)
        | .error s!"is_eq_term: could not infer type of {λA;b}"
      let has_type_x ← has_type f Γ x A
      let has_type_b ← has_type f (Γ ⬝ A) b B
      let is_eq_term_b ← is_eq_term f Γ (b⌈x⌉₀) t (B⌈x⌉₀)
      let is_eq_type_B_T ← is_eq_type f Γ (B⌈x⌉₀) T
      have pi_comp := IsEqualTerm.pi_comp has_type_b.down has_type_x.down
      have := IsEqualTerm.term_trans pi_comp is_eq_term_b.down
      return .up <| IsEqualTerm.ty_conv_eq this is_eq_type_B_T.down
    | f+1, Γ, .indSigma A B C c (a&b), t, T => do
      let has_type_a ← has_type f Γ a A
      let has_type_b ← has_type f Γ b (B⌈a⌉₀)
      let is_type_C ← is_type f _ (Γ ⬝ ΣA;B) C
      let has_type_c ← has_type f (Γ ⬝ A ⬝ B) c (C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)
      have sigma_comp := IsEqualTerm.sigma_comp is_type_C.down has_type_c.down has_type_a.down has_type_b.down
      let is_eq_term_c ← is_eq_term f Γ (c⌈(ₛidₚ)⋄ a⋄ b⌉) t (C⌈a&b⌉₀)
      let is_eq_type_C_T ← is_eq_type f Γ (C⌈a&b⌉₀) T
      have := IsEqualTerm.term_trans sigma_comp is_eq_term_c.down
      return .up <| IsEqualTerm.ty_conv_eq this is_eq_type_C_T.down
    | f+1, Γ, .indNat A z s 𝓏, t, T => do
      let is_type_A ← is_type f _ (Γ ⬝ 𝒩) A
      let has_type_z ← has_type f Γ z (A⌈𝓏⌉₀)
      let has_type_s ← has_type f (Γ ⬝ 𝒩 ⬝ A) s (A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
      let has_type_zero ← has_type f Γ 𝓏 𝒩
      have nat_zero_comp := IsEqualTerm.nat_zero_comp is_type_A.down has_type_z.down has_type_s.down has_type_zero.down
      let is_eq_term_z ← is_eq_term f Γ z t (A⌈𝓏⌉₀)
      let is_eq_type_A_T ← is_eq_type f Γ (A⌈𝓏⌉₀) T
      have := IsEqualTerm.term_trans nat_zero_comp is_eq_term_z.down
      return .up <| IsEqualTerm.ty_conv_eq this is_eq_type_A_T.down
    | f+1, Γ, .indNat A z s 𝓈(n), t, T => do
      let is_type_A ← is_type f _ (Γ ⬝ 𝒩) A
      let has_type_z ← has_type f Γ z (A⌈𝓏⌉₀)
      let has_type_s ← has_type f (Γ ⬝ 𝒩 ⬝ A) s (A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)
      let has_type_n ← has_type f Γ n 𝒩
      have nat_succ_comp := IsEqualTerm.nat_succ_comp is_type_A.down has_type_z.down has_type_s.down has_type_n.down
      let is_eq_term_s ← is_eq_term f Γ (s⌈(ₛidₚ)⋄ n⋄ (.indNat A z s n)⌉) t (A⌈𝓈(n)⌉₀)
      let is_eq_type_A_T ← is_eq_type f Γ (A⌈𝓈(n)⌉₀) T
      have := IsEqualTerm.term_trans nat_succ_comp is_eq_term_s.down
      return .up <| IsEqualTerm.ty_conv_eq this is_eq_type_A_T.down
    -- TODO: add J computation rule here
    -- congruence rules
    | f+1, Γ, ⋆, ⋆, 𝟙 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.unit_intro_eq ctx_ok.down
    | f+1, Γ, (.indUnit A b a), (.indUnit A' b' a'), Asubst => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=A⌈b⌉₀) (B:=Asubst)
        · apply IsEqualTerm.unit_elim_eq
          · exact (← is_eq_type f (Γ ⬝ 𝟙) A A').down
          · exact (← is_eq_term f Γ a a' (A⌈⋆⌉₀)).down
          · exact (← is_eq_term f Γ b b' 𝟙).down
        · exact (← is_eq_type f Γ (A⌈b⌉₀) Asubst).down
    /-| f+1, Γ, .indEmpty A b, .indEmpty A' b', Asubst => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=A⌈b⌉₀) (B:=Asubst)
        · apply IsEqualTerm.empty_elim_eq
          · exact (← is_eq_type f (Γ ⬝ 𝟘) A A').down
          · exact (← is_eq_term f Γ b b' 𝟘).down
        · exact (← is_eq_type f Γ (A⌈b⌉₀) Asubst).down
    | f+1, Γ, λA;b, λA';b', ΠT;T' => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=ΠA;T') (B:=ΠT;T')
        · apply IsEqualTerm.pi_intro_eq
          · exact (← is_eq_term f (Γ ⬝ A) b b' T').down
          · exact (← is_eq_type f Γ A A').down
        · exact (← is_eq_type f Γ (ΠA;T') (ΠT;T')).down
    | f+1, Γ, func◃a, func'◃a', T => do
      let ⟨ΠA;B, _⟩ ← infer_type f Γ (func◃a)
        | .error s!"is_eq_term: could not infer type of {func◃a}"
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=B⌈a⌉₀) (B:=T)
        · apply IsEqualTerm.pi_elim_eq
          · exact (← is_eq_term f Γ func func' (ΠA;B)).down
          · exact (← is_eq_term f Γ a a' A).down
        · exact (← is_eq_type f Γ (B⌈a⌉₀) T).down
    | f+1, Γ, a&b, a'&b', ΣA;B => do
      return .up <| by
        apply IsEqualTerm.sigma_intro_eq
        · exact (← is_eq_term f Γ a a' A).down
        · exact (← is_eq_term f Γ b b' (B⌈a⌉₀)).down
        · exact (← is_type f _ (Γ ⬝ A) B).down-/
    | f+1, Γ, .indSigma A B C c p, .indSigma A' B' C' c' p', T => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=C⌈p⌉₀) (B:=T)
        · apply IsEqualTerm.sigma_elim_eq
          · exact (← is_eq_type f (Γ ⬝ ΣA;B) C C').down
          · exact (← is_eq_term f (Γ ⬝ A ⬝ B) c c' (C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)).down
          · exact (← is_eq_type f Γ A A').down
          · exact (← is_eq_type f (Γ ⬝ A) B B').down
          · exact (← is_eq_term f Γ p p' (ΣA;B)).down
        · exact (← is_eq_type f Γ (C⌈p⌉₀) T).down
    | f+1, Γ, 𝓏, 𝓏, 𝒩 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.nat_zero_intro_eq ctx_ok.down
    | f+1, Γ, 𝓈(n), 𝓈(n'), 𝒩 => do
      let is_eq_term_n ← is_eq_term f Γ n n' 𝒩
      return .up <| IsEqualTerm.nat_succ_intro_eq is_eq_term_n.down
    /-| f+1, Γ, .indNat A z s n, .indNat A' z' s' n', T => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=A⌈n⌉₀) (B:=T)
        · apply IsEqualTerm.nat_elim_eq
          · exact (← is_eq_type f (Γ ⬝ 𝒩) A A').down
          · exact (← is_eq_term f Γ z z' (A⌈𝓏⌉₀)).down
          · exact (← is_eq_term f (Γ ⬝ 𝒩 ⬝ A) s s' (A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)).down
          · exact (← is_eq_term f Γ n n' 𝒩).down
        · exact (← is_eq_type f Γ (A⌈n⌉₀) T).down
    | f+1, Γ, .refl A a, .refl A' a', T => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=(.iden A a a)) (B:=T)
        · apply IsEqualTerm.iden_intro_eq
          · exact (← is_eq_type f Γ A A').down
          · exact (← is_eq_term f Γ a a' A).down
        · exact (← is_eq_type f Γ (.iden A a a) T).down
    | f+1, Γ, .j A B b a₁ a₃ p, .j A' B' b' a₂ a₄ p', T => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=B⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉) (B:=T)
        · apply IsEqualTerm.iden_elim_eq
          · exact (← is_eq_type f (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) B B').down
          · exact (← is_eq_term f (Γ ⬝ A) b b' (B⌈(ₛidₚ)⋄ v(0)⋄ .refl (A⌊↑ₚidₚ⌋) v(0)⌉)).down
          · exact (← is_eq_type f Γ A A').down
          · exact (← is_eq_term f Γ a₁ a₂ A).down
          · exact (← is_eq_term f Γ a₃ a₄ A').down
          · exact (← is_eq_term f Γ p p' (a₁ ≃[A] a₃)).down
        · exact (← is_eq_type f Γ (B⌈(ₛidₚ)⋄ a₁⋄ a₃⋄ p⌉) T).down-/
    -- univ rules
    | f+1, Γ, 𝟙, 𝟙, Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ 𝒰 Univ
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_unit_eq ctx_ok.down) is_eq_type_U_Univ.down
    | f+1, Γ, 𝟘, 𝟘, Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ 𝒰 Univ
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_empty_eq ctx_ok.down) is_eq_type_U_Univ.down
    | f+1, Γ, ΠA;B, ΠA';B', Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ 𝒰 Univ
      let is_eq_term_A_A' ← is_eq_term f Γ A A' 𝒰
      let is_eq_term_B_B' ← is_eq_term f (Γ ⬝ A) B B' 𝒰
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_pi_eq is_eq_term_A_A'.down is_eq_term_B_B'.down) is_eq_type_U_Univ.down
    | f+1, Γ, ΣA;B, ΣA';B', Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ 𝒰 Univ
      let is_eq_term_A_A' ← is_eq_term f Γ A A' 𝒰
      let is_eq_term_B_B' ← is_eq_term f (Γ ⬝ A) B B' 𝒰
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_sigma_eq is_eq_term_A_A'.down is_eq_term_B_B'.down) is_eq_type_U_Univ.down
    | f+1, Γ, 𝒩, 𝒩, Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ 𝒰 Univ
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_nat_eq ctx_ok.down) is_eq_type_U_Univ.down
    | f+1, Γ, a₁ ≃[A] a₂, a₃ ≃[A'] a₄ , Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ 𝒰 Univ
      let is_eq_term_A_A' ← is_eq_term f Γ A A' 𝒰
      let is_eq_term_a₁_a₃ ← is_eq_term f Γ a₁ a₃ A
      let is_eq_term_a₂_a₄ ← is_eq_term f Γ a₂ a₄ A
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_iden_eq
          is_eq_term_A_A'.down is_eq_term_a₁_a₃.down is_eq_term_a₂_a₄.down) is_eq_type_U_Univ.down-/
    -- conversion
    | f+1, Γ, a, a', A => do
      let is_eq_symm ← is_eq_term f Γ a' a A
      return .up <| IsEqualTerm.term_symm is_eq_symm.down
  termination_by structural fuel

  def infer_type (fuel : Nat) (Γ : ACtx n) (t : ATm n) :
      Except String (Σ' T : ATm n, Γ.toCtx ⊢ t.toTm ∶ T.toTm) :=
    match fuel, Γ, t with
    | 0, _, _ => .error "infer_type: out of fuel"
    | f+1, Γ, .tt => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.unit, HasType.unit_intro ctx_ok.down⟩
    | f+1, Γ, .zeroNat => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.nat, HasType.nat_zero_intro ctx_ok.down⟩
    | f+1, Γ, .succNat n => do
      let is_nat_n ← has_type f Γ n .nat
      return ⟨.nat, HasType.nat_succ_intro is_nat_n.down⟩
    | f+1, Γ, .unit => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.univ, HasType.univ_unit ctx_ok.down⟩
    | f+1, Γ, .nat => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.univ, HasType.univ_nat ctx_ok.down⟩
    | f+1, ACtx.extend _ Γ T, .var 0 => do
      let is_type_T ← is_type f _ Γ T
      return ⟨(T⌊ₐ↑ₚidₚ⌋),
          ((toTm_weak _ _) ▸ (toCtx_extend _ _ _) ▸ HasType.var is_type_T.down)⟩
    | f+1, ACtx.extend _ Γ T, .var ⟨(i+1), hi⟩ => do
      let ⟨T', h⟩ ← infer_type f Γ <| .var ⟨i, Nat.succ_lt_succ_iff.mp hi⟩
      let is_type_T ← is_type f _ Γ T
      return ⟨(T'⌊ₐ↑ₚidₚ⌋), (toTm_weak _ _) ▸ (toCtx_extend _ _ _) ▸ HasType.weak h is_type_T.down⟩
    | f+1, Γ, .lam A b => do
      let ⟨B, h⟩ ← infer_type f (Γ ⬝a A) b
      return ⟨.pi A B, HasType.pi_intro h⟩
    | f+1, Γ, .pairSigma a b B => do
      let ⟨A, ha⟩ ← infer_type f Γ a
      let hb ← has_type f Γ b (B⌈ₐa⌉₀)
      let is_type_B ← is_type f _ (Γ ⬝a A) B
      return ⟨.sigma A B, HasType.sigma_intro ha ((toTm_subst _ _) ▸ hb.down) is_type_B.down⟩
    | f+1, Γ, .app g a => do
      let ⟨.pi A B, hg⟩ ← infer_type f Γ g
        | .error s!"infer_type: expected a lambda term at {g.toTm}"
      let has_type_a ← has_type f Γ a A
      return ⟨B⌈ₐa⌉₀, (toTm_subst _ _) ▸ HasType.pi_elim hg has_type_a.down⟩
    | f+1, _, t => .error s!"infer_type: unsupported pattern {t.toTm}"
  termination_by structural fuel
end
