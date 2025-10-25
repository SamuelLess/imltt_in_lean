import IMLTT.typed.JudgmentsAndRules
import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Elaboration
import IMLTT.typed.annotated.Substitution
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

def is_ctx : ((k : Nat) → (Γsome : ACtx k) → (T : ATm k) →
    Except String (PLift (Γsome.toCtx ⊢ T.toTm type)))
    → (Γ : ACtx n) → Except String (PLift (Γ.toCtx ctx))
  | _, .empty => pure <| .up IsCtx.empty
  | my_is_type, ACtx.extend _ Γ' T' => do
    let ctx_ok ← is_ctx my_is_type Γ'
    let t_ok : PLift (Γ'.toCtx ⊢ T'.toTm type) ← my_is_type _ Γ' T'
    return .up <| IsCtx.extend ctx_ok.down t_ok.down

notation Γ "⬝a" A => ACtx.extend Lean.Name.anonymous Γ A

set_option maxHeartbeats 800000
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
        · let h := (← has_type f ((Γ ⬝a A) ⬝a B) c (C⌈ₐ(ₐₛ↑ₚ↑ₚidₚ)⋄ₐ
            (.pairSigma (.var 1) (.var 0) (B⌊ₐ↑ₚ↑ₚidₚ⌋))⌉)).down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_asubst] at h
          exact h
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
        · let h := (← has_type f ((Γ ⬝a .nat) ⬝a A) s
            (A⌈ₐ(ₐₛ↑ₚidₚ)⋄ₐ (.succNat <| .var 0)⌉⌊ₐ↑ₚidₚ⌋)).down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_weak] at h
          rewrite [toTm_asubst] at h
          exact h
        · exact (← has_type f Γ n .nat).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (A⌈ₐn⌉₀) A').down
    | f+1, Γ, .j A B b a a' p, B' => do
      return .up <| by
        apply HasType.ty_conv (B:=B'.toTm)
        apply HasType.iden_elim
        · let h := (← is_type f _ (((Γ ⬝a A) ⬝a A⌊ₐ↑ₚidₚ⌋) ⬝a
            (.iden (A⌊ₐ↑ₚ↑ₚidₚ⌋) (.var 1) (.var 0))) B).down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_weak] at h
          simp [ATm.toTm] at h
          rewrite [toTm_weak] at h
          exact h
        · let h := (← has_type f (Γ ⬝a A) b (B⌈ₐ(ₐₛidₚ)⋄ₐ (.var 0)⋄ₐ
            .refl (A⌊ₐ↑ₚidₚ⌋) (.var 0)⌉)).down
          rewrite [toCtx_extend] at h
          --rewrite [toTm_weak] at h
          rewrite [toTm_asubst] at h
          simp [ASubst.toSubst, ATm.toTm] at h
          rewrite [toTm_weak] at h
          exact h
        · exact (← has_type f Γ a A).down
        · exact (← has_type f Γ a' A).down
        · exact (← has_type f Γ p (.iden A a a')).down
        · let h := (← is_eq_type f Γ (B⌈ₐ(ₐₛidₚ)⋄ₐ a⋄ₐ a'⋄ₐ p⌉) B').down
          rewrite [toTm_asubst] at h
          exact h
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

  def is_eq_term (fuel: Nat) (Γ : ACtx n) (a : ATm n) (a' : ATm n) (A : ATm n) :
      Except String (PLift (Γ.toCtx ⊢ a.toTm ≡ a'.toTm ∶ A.toTm)) :=
    match fuel, Γ, a, a', A with
    | 0, Γ, a, a', A =>
      .error s!"is_eq_term: out of fuel with {Γ} ⊢ {a.toTm} ≡ {a'.toTm} : {A.toTm}"
    -- variables
    | f+1, ACtx.extend _ Γ T, .var 0, .var 0, T' => do
      let is_type_T ← is_type f _ Γ T
      let is_eq_T_T' ← is_eq_type f (Γ ⬝a T) (T⌊ₐ↑ₚidₚ⌋) T'
      have := IsEqualTerm.var_eq is_type_T.down
      return .up <| IsEqualTerm.ty_conv_eq this ((toTm_weak _ _) ▸ is_eq_T_T'.down)
    | f+1, ACtx.extend _ Γ T, .var ⟨i+1,hi⟩, .var ⟨j+1,hj⟩, T' => do
      if hieqj : i == j then
        let ⟨Tvi, htvi⟩ ← infer_type f Γ (.var (⟨i, (Nat.succ_lt_succ_iff.mp hi)⟩))
        have t : (Γ ⬝a T).toCtx ⊢ v(⟨i+1, hi⟩) ≡ v(⟨j+1, hj⟩) ∶ T'.toTm := by
          simp only [beq_iff_eq.mp hieqj |>.symm]
          rw [←Fin.succ_mk]
          apply IsEqualTerm.ty_conv_eq
          apply IsEqualTerm.weak_eq
          · exact defeq_refl_term htvi
          · exact (← is_type f _ Γ T).down
          · exact (toTm_weak _ _) ▸ (← is_eq_type f (Γ ⬝a T) (Tvi⌊ₐ↑ₚidₚ⌋) T').down
          · exact Nat.succ_lt_succ_iff.mp hi
        return .up t
      else
        .error s!"is_eq_term: two different variables cannot defeq v({i}) ≡ v({j}) ∶ {T'.toTm}"
    -- computation rules
    | f+1, Γ, .indUnit A .tt a, a', A' => do
      let is_type_A ← is_type f _ (Γ ⬝a .unit) A
      let has_type_a ← has_type f Γ a (A⌈ₐ.tt⌉₀)
      let is_eq_term_a_a' ← is_eq_term f Γ a a' (A⌈ₐ.tt⌉₀)
      let is_eq_type_A_A' ← is_eq_type f Γ (A⌈ₐ.tt⌉₀) A'
      have unit_comp := IsEqualTerm.unit_comp is_type_A.down <| (toTm_subst _ .tt) ▸ has_type_a.down
      have term_trans := IsEqualTerm.term_trans unit_comp <|
        (toTm_subst _ .tt) ▸ is_eq_term_a_a'.down
      return .up <| IsEqualTerm.ty_conv_eq term_trans <| (toTm_subst _ .tt) ▸ is_eq_type_A_A'.down
    | f+1, Γ, .app (.lam A b) x, t, T => do
      let ⟨.pi _ B, _⟩ ← infer_type f Γ (.lam A b)
        | .error s!"is_eq_term: could not infer type of λ{A};{b}"
      let has_type_x ← has_type f Γ x A
      let has_type_b ← has_type f (Γ ⬝a A) b B
      let is_eq_term_b ← is_eq_term f Γ (b⌈ₐx⌉₀) t (B⌈ₐx⌉₀)
      let is_eq_type_B_T ← is_eq_type f Γ (B⌈ₐx⌉₀) T
      have pi_comp := IsEqualTerm.pi_comp has_type_b.down has_type_x.down
      have := IsEqualTerm.term_trans pi_comp <|
        (toTm_subst _ _) ▸ (toTm_subst _ _) ▸ is_eq_term_b.down
      return .up <| IsEqualTerm.ty_conv_eq this <| (toTm_subst _ _) ▸ is_eq_type_B_T.down
    | f+1, Γ, .indSigma A B C c (.pairSigma a b S), t, T => do
      let has_type_a ← has_type f Γ a A
      let has_type_b ← has_type f Γ b (B⌈ₐa⌉₀)
      let is_type_C ← is_type f _ (Γ ⬝a (.sigma A B)) C
      let has_type_c ← has_type f ((Γ ⬝a A) ⬝a B) c (C⌈ₐ(ₐₛ↑ₚ↑ₚidₚ)⋄ₐ
        .pairSigma (.var 1) (.var 0) (B⌊ₐ↑ₚ↑ₚidₚ⌋)⌉)
      have sigma_comp := IsEqualTerm.sigma_comp is_type_C.down
        (by
          let h := has_type_c.down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_asubst] at h
          exact h)
        has_type_a.down
        ((toTm_subst _ _ ) ▸ has_type_b.down)
      let is_eq_term_c ← is_eq_term f Γ (c⌈ₐ(ₐₛidₚ)⋄ₐ a⋄ₐ b⌉) t (C⌈ₐ.pairSigma a b B⌉₀)
      let is_eq_type_C_T ← is_eq_type f Γ (C⌈ₐ.pairSigma a b B⌉₀) T
      have := IsEqualTerm.term_trans sigma_comp <| by
        let h := is_eq_term_c.down
        rewrite [toTm_asubst] at h
        rewrite [toTm_subst] at h
        exact h
      return .up <| IsEqualTerm.ty_conv_eq this <|
        (toTm_subst _ (a.pairSigma b B)) ▸ is_eq_type_C_T.down
    | f+1, Γ, .indNat A z s .zeroNat, t, T => do
      let is_type_A ← is_type f _ (Γ ⬝a .nat) A
      let has_type_z ← has_type f Γ z (A⌈ₐ.zeroNat⌉₀)
      let has_type_s ← has_type f ((Γ ⬝a .nat) ⬝a A) s (A⌈ₐ(ₐₛ↑ₚidₚ)⋄ₐ (.succNat (.var 0))⌉⌊ₐ↑ₚidₚ⌋)
      let has_type_zero ← has_type f Γ .zeroNat .nat
      have nat_zero_comp := IsEqualTerm.nat_zero_comp is_type_A.down
        ((toTm_subst _ .zeroNat) ▸ has_type_z.down)
        (by
          let h := has_type_s.down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_weak] at h
          rewrite [toTm_asubst] at h
          exact h)
        has_type_zero.down
      let is_eq_term_z ← is_eq_term f Γ z t (A⌈ₐ.zeroNat⌉₀)
      let is_eq_type_A_T ← is_eq_type f Γ (A⌈ₐ.zeroNat⌉₀) T
      have := IsEqualTerm.term_trans nat_zero_comp <| (toTm_subst _ .zeroNat) ▸ is_eq_term_z.down
      return .up <| IsEqualTerm.ty_conv_eq this <| (toTm_subst _ .zeroNat) ▸ is_eq_type_A_T.down
    | f+1, Γ, .indNat A z s (.succNat n), t, T => do
      let is_type_A ← is_type f _ (Γ ⬝a .nat) A
      let has_type_z ← has_type f Γ z (A⌈ₐ.zeroNat⌉₀)
      let has_type_s ← has_type f ((Γ ⬝a .nat) ⬝a A) s (A⌈ₐ(ₐₛ↑ₚidₚ)⋄ₐ (.succNat (.var 0))⌉⌊ₐ↑ₚidₚ⌋)
      let has_type_n ← has_type f Γ n .nat
      have nat_succ_comp := IsEqualTerm.nat_succ_comp is_type_A.down
        ((toTm_subst _ .zeroNat) ▸ has_type_z.down)
        (by
          let h := has_type_s.down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_weak] at h
          rewrite [toTm_asubst] at h
          exact h)
        has_type_n.down
      let is_eq_term_s ← is_eq_term f Γ (s⌈ₐ(ₐₛidₚ)⋄ₐ n⋄ₐ (.indNat A z s n)⌉) t (A⌈ₐ(.succNat n)⌉₀)
      let is_eq_type_A_T ← is_eq_type f Γ (A⌈ₐ(.succNat n)⌉₀) T
      have := IsEqualTerm.term_trans nat_succ_comp <| by
        let h := is_eq_term_s.down
        rewrite [toTm_asubst] at h
        rewrite [toTm_subst] at h
        exact h
      return .up <| IsEqualTerm.ty_conv_eq this ((toTm_subst _ (.succNat n)) ▸ is_eq_type_A_T.down)
    | f+1, Γ, .j A B b a₁ a₂ (.refl A_refl a_refl), t, T => do
      let is_type_B ← is_type f _ (((Γ ⬝a A) ⬝a A⌊ₐ↑ₚidₚ⌋) ⬝a
        (.iden (A⌊ₐ↑ₚ↑ₚidₚ⌋) (.var 1) (.var 0))) B
      let has_type_b ← has_type f (Γ ⬝a A) b (B⌈ₐ(ₐₛidₚ)⋄ₐ (.var 0)⋄ₐ .refl (A⌊ₐ↑ₚidₚ⌋) (.var 0)⌉)
      let has_type_a_refl ← has_type f Γ a_refl A
      have iden_comp := IsEqualTerm.iden_comp
        (by
          let h := is_type_B.down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_weak] at h
          simp [ATm.toTm] at h
          rewrite [toTm_weak] at h
          exact h)
        (by
          let h := has_type_b.down
          rewrite [toCtx_extend] at h
          rewrite [toTm_asubst] at h
          simp [ASubst.toSubst, ATm.toTm] at h
          rewrite [toTm_weak] at h
          exact h)
        has_type_a_refl.down
      -- Now connect to the target
      let is_eq_term_b ← is_eq_term f Γ (b⌈ₐa_refl⌉₀) t
        (B⌈ₐ(ₐₛidₚ)⋄ₐ a_refl⋄ₐ a_refl⋄ₐ .refl A a_refl⌉)
      let is_eq_type_B_T ← is_eq_type f Γ (B⌈ₐ(ₐₛidₚ)⋄ₐ a_refl⋄ₐ a_refl⋄ₐ .refl A a_refl⌉) T
      have term_trans := IsEqualTerm.term_trans iden_comp <| by
        let h := is_eq_term_b.down
        simp [toTm_asubst] at h ⊢
        exact h
      return .up <| by
        apply IsEqualTerm.ty_conv_eq
          (A:=B.toTm⌈(ₛidₚ)⋄ a_refl.toTm⋄ a_refl.toTm⋄ A.toTm.refl a_refl.toTm⌉)
        · apply IsEqualTerm.term_symm
          have term_trans_symm := IsEqualTerm.term_symm term_trans
          have := IsEqualTerm.term_trans
            (c:=(A.j B b a₁ a₂ (A_refl.refl a_refl)).toTm) term_trans_symm
          apply this
          let is_eq_term_j := (← is_eq_term f Γ (A.j B b a_refl a_refl (A.refl a_refl))
            (A.j B b a₁ a₂ (A_refl.refl a_refl))
              (B⌈ₐ(ₐₛidₚ)⋄ₐ a_refl⋄ₐ a_refl⋄ₐ A.refl a_refl⌉)).down
          simp [toTm_asubst] at is_eq_term_j
          exact is_eq_term_j
        · let h := is_eq_type_B_T.down
          simp [toTm_asubst] at h ⊢
          exact h
    -- congruence rules
    | f+1, Γ,.tt, .tt, .unit => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.unit_intro_eq ctx_ok.down
    | f+1, Γ, (.indUnit A b a), (.indUnit A' b' a'), Asubst => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=A.toTm⌈b.toTm⌉₀) (B:=Asubst.toTm)
        · apply IsEqualTerm.unit_elim_eq
          · exact (← is_eq_type f (Γ ⬝a .unit) A A').down
          · exact (toTm_subst _ .tt) ▸ (← is_eq_term f Γ a a' (A⌈ₐ.tt⌉₀)).down
          · exact (← is_eq_term f Γ b b' .unit).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (A⌈ₐb⌉₀) Asubst).down
    | f+1, Γ, .indEmpty A b, .indEmpty A' b', Asubst => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=A.toTm⌈b.toTm⌉₀) (B:=Asubst.toTm)
        · apply IsEqualTerm.empty_elim_eq
          · exact (← is_eq_type f (Γ ⬝a .empty) A A').down
          · exact (← is_eq_term f Γ b b' .empty).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (A⌈ₐb⌉₀) Asubst).down
    | f+1, Γ, .lam A b, .lam A' b', .pi T T' => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=ΠA.toTm;T'.toTm) (B:=ΠT.toTm;T'.toTm)
        · apply IsEqualTerm.pi_intro_eq
          · exact (← is_eq_term f (Γ ⬝a A) b b' T').down
          · exact (← is_eq_type f Γ A A').down
        · exact (← is_eq_type f Γ (.pi A T') (.pi T T')).down
    | f+1, Γ, .app func a, .app func' a', T => do
      let ⟨.pi A B, _⟩ ← infer_type f Γ (.app func a)
        | .error s!"is_eq_term: could not infer type of {func}◃{a}"
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=B.toTm⌈a.toTm⌉₀) (B:=T.toTm)
        · apply IsEqualTerm.pi_elim_eq
          · exact (← is_eq_term f Γ func func' (.pi A B)).down
          · exact (← is_eq_term f Γ a a' A).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (B⌈ₐa⌉₀) T).down
    | f+1, Γ, .pairSigma a b S, .pairSigma a' b' S', .sigma A B => do
      return .up <| by
        apply IsEqualTerm.sigma_intro_eq
        · exact (← is_eq_term f Γ a a' A).down
        · exact (toTm_subst _ _) ▸ (← is_eq_term f Γ b b' (B⌈ₐa⌉₀)).down
        · exact (← is_type f _ (Γ ⬝a A) B).down
    | f+1, Γ, .indSigma A B C c p, .indSigma A' B' C' c' p', T => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=C.toTm⌈p.toTm⌉₀) (B:=T.toTm)
        · apply IsEqualTerm.sigma_elim_eq
          · exact (← is_eq_type f (Γ ⬝a .sigma A B) C C').down
          · let h := (← is_eq_term f ((Γ ⬝a A) ⬝a B) c c'
              (C⌈ₐ(ₐₛ↑ₚ↑ₚidₚ)⋄ₐ .pairSigma (.var 1) (.var 0) (B⌊ₐ↑ₚ↑ₚidₚ⌋)⌉)).down
            rewrite [toCtx_extend] at h
            rewrite [toCtx_extend] at h
            rewrite [toTm_asubst] at h
            simp [ASubst.toSubst, ATm.toTm] at h
            exact h
          · exact (← is_eq_type f Γ A A').down
          · exact (← is_eq_type f (Γ ⬝a A) B B').down
          · exact (← is_eq_term f Γ p p' (.sigma A B)).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (C⌈ₐp⌉₀) T).down
    | f+1, Γ, .zeroNat, .zeroNat, .nat => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.nat_zero_intro_eq ctx_ok.down
    | f+1, Γ, .succNat n , .succNat n', .nat => do
      let is_eq_term_n ← is_eq_term f Γ n n' .nat
      return .up <| IsEqualTerm.nat_succ_intro_eq is_eq_term_n.down
    | f+1, Γ, .indNat A z s n, .indNat A' z' s' n', T => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=A.toTm⌈n.toTm⌉₀) (B:=T.toTm)
        · apply IsEqualTerm.nat_elim_eq
          · exact (← is_eq_type f (Γ ⬝a .nat) A A').down
          · exact (toTm_subst _ .zeroNat) ▸ (← is_eq_term f Γ z z' (A⌈ₐ.zeroNat⌉₀)).down
          · let h := (← is_eq_term f ((Γ ⬝a .nat) ⬝a A) s s'
              (A⌈ₐ(ₐₛ↑ₚidₚ)⋄ₐ .succNat (.var 0)⌉⌊ₐ↑ₚidₚ⌋)).down
            rewrite [toCtx_extend] at h
            rewrite [toCtx_extend] at h
            rewrite [toTm_weak] at h
            rewrite [toTm_asubst] at h
            simp_all [ASubst.toSubst, ATm.toTm]
          · exact (← is_eq_term f Γ n n' .nat).down
        · exact (toTm_subst _ _) ▸ (← is_eq_type f Γ (A⌈ₐn⌉₀) T).down
    | f+1, Γ, .refl A a, .refl A' a', T => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=(Tm.iden A.toTm a.toTm a.toTm)) (B:=T.toTm)
        · apply IsEqualTerm.iden_intro_eq
          · exact (← is_eq_type f Γ A A').down
          · exact (← is_eq_term f Γ a a' A).down
        · exact (← is_eq_type f Γ (.iden A a a) T).down
    | f+1, Γ, .j A B b a₁ a₃ p, .j A' B' b' a₂ a₄ p', T => do
      return .up <| by
        apply IsEqualTerm.ty_conv_eq (A:=B.toTm⌈(ₛidₚ)⋄ a₁.toTm ⋄ a₃.toTm ⋄ p.toTm⌉) (B:=T.toTm)
        · apply IsEqualTerm.iden_elim_eq
          · let h := (← is_eq_type f
              (((Γ ⬝a A) ⬝a (A⌊ₐ↑ₚidₚ⌋)) ⬝a ((A⌊ₐ↑ₚ↑ₚidₚ⌋).iden (.var 1) (.var 0))) B B').down
            rewrite [toCtx_extend] at h
            rewrite [toCtx_extend] at h
            rewrite [toCtx_extend] at h
            rewrite [toTm_weak] at h
            simp [ATm.toTm] at h
            rewrite [toTm_weak] at h
            exact h
          · let h := (← is_eq_term f (Γ ⬝a A) b b'
              (B⌈ₐ(ₐₛidₚ)⋄ₐ .var 0 ⋄ₐ .refl (A⌊ₐ↑ₚidₚ⌋) (.var 0)⌉)).down
            rewrite [toCtx_extend] at h
            rewrite [toTm_asubst] at h
            simp [ASubst.toSubst, ATm.toTm] at h
            rewrite [toTm_weak] at h
            exact h
          · exact (← is_eq_type f Γ A A').down
          · exact (← is_eq_term f Γ a₁ a₂ A).down
          · exact (← is_eq_term f Γ a₃ a₄ A').down
          · exact (← is_eq_term f Γ p p' (A.iden a₁ a₃)).down
        · let h := (← is_eq_type f Γ (B⌈ₐ(ₐₛidₚ)⋄ₐ a₁⋄ₐ a₃⋄ₐ p⌉) T).down
          rewrite [toTm_asubst] at h
          exact h
    -- univ rules
    | f+1, Γ, .unit, .unit, Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ .univ Univ
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_unit_eq ctx_ok.down) is_eq_type_U_Univ.down
    | f+1, Γ, .empty, .empty, Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ .univ Univ
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_empty_eq ctx_ok.down) is_eq_type_U_Univ.down
    | f+1, Γ, .pi A B, .pi A' B', Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ .univ Univ
      let is_eq_term_A_A' ← is_eq_term f Γ A A' .univ
      let is_eq_term_B_B' ← is_eq_term f (Γ ⬝a A) B B' .univ
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_pi_eq is_eq_term_A_A'.down is_eq_term_B_B'.down) is_eq_type_U_Univ.down
    | f+1, Γ, .sigma A B, .sigma A' B', Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ .univ Univ
      let is_eq_term_A_A' ← is_eq_term f Γ A A' .univ
      let is_eq_term_B_B' ← is_eq_term f (Γ ⬝a A) B B' .univ
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_sigma_eq is_eq_term_A_A'.down is_eq_term_B_B'.down) is_eq_type_U_Univ.down
    | f+1, Γ, .nat, .nat, Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ .univ Univ
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_nat_eq ctx_ok.down) is_eq_type_U_Univ.down
    | f+1, Γ, .iden A a₁ a₂, .iden A' a₃ a₄ , Univ => do
      let is_eq_type_U_Univ ← is_eq_type f Γ .univ Univ
      let is_eq_term_A_A' ← is_eq_term f Γ A A' .univ
      let is_eq_term_a₁_a₃ ← is_eq_term f Γ a₁ a₃ A
      let is_eq_term_a₂_a₄ ← is_eq_term f Γ a₂ a₄ A
      return .up <| IsEqualTerm.ty_conv_eq
        (IsEqualTerm.univ_iden_eq
          is_eq_term_A_A'.down is_eq_term_a₁_a₃.down is_eq_term_a₂_a₄.down) is_eq_type_U_Univ.down
    -- conversion
    | f+1, Γ, a, a', A => do
      let is_eq_symm ← is_eq_term f Γ a' a A
      return .up <| IsEqualTerm.term_symm is_eq_symm.down
  termination_by structural fuel

  def infer_type (fuel : Nat) (Γ : ACtx n) (t : ATm n) :
      Except String (Σ' T : ATm n, Γ.toCtx ⊢ t.toTm ∶ T.toTm) :=
    match fuel, Γ, t with
    | 0, _, _ => .error "infer_type: out of fuel"
    -- 'types'
    | f+1, Γ, .unit => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.univ, HasType.univ_unit ctx_ok.down⟩
    | f+1, Γ, .empty => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.univ, HasType.univ_empty ctx_ok.down⟩
    | f+1, Γ, .pi A B => do
      let has_type_A ← has_type f Γ A .univ
      let has_type_B ← has_type f (Γ ⬝a A) B .univ
      return ⟨.univ, HasType.univ_pi has_type_A.down has_type_B.down⟩
    | f+1, Γ, .sigma A B => do
      let has_type_A ← has_type f Γ A .univ
      let has_type_B ← has_type f (Γ ⬝a A) B .univ
      return ⟨.univ, HasType.univ_sigma has_type_A.down has_type_B.down⟩
    | f+1, Γ, .nat => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.univ, HasType.univ_nat ctx_ok.down⟩
    | f+1, Γ, .iden A a₁ a₂ => do
      have univ_eq : Tm.univ = ATm.univ.toTm := by simp [ATm.toTm]
      let has_type_a₀ ← has_type f Γ A .univ
      let has_type_a₁ ← has_type f Γ a₁ A
      let has_type_a₂ ← has_type f Γ a₂ A
      return ⟨.univ,
        HasType.univ_iden (univ_eq ▸ has_type_a₀.down) has_type_a₁.down has_type_a₂.down⟩
    -- 'terms'
    | f+1, ACtx.extend _ Γ T, .var 0 => do
      let is_type_T ← is_type f _ Γ T
      return ⟨(T⌊ₐ↑ₚidₚ⌋),
          ((toTm_weak _ _) ▸ (toCtx_extend _ _ _) ▸ HasType.var is_type_T.down)⟩
    | f+1, ACtx.extend _ Γ T, .var ⟨(i+1), hi⟩ => do
      let ⟨T', h⟩ ← infer_type f Γ <| .var ⟨i, Nat.succ_lt_succ_iff.mp hi⟩
      let is_type_T ← is_type f _ Γ T
      return ⟨(T'⌊ₐ↑ₚidₚ⌋), (toTm_weak _ _) ▸ (toCtx_extend _ _ _) ▸ HasType.weak h is_type_T.down⟩
    | f+1, Γ, .tt => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.unit, HasType.unit_intro ctx_ok.down⟩
    | f+1, Γ, .indUnit A b a => do
      let is_type_A ← is_type f _ (Γ ⬝a .unit) A
      let has_type_a ← has_type f Γ a (A⌈ₐ.tt⌉₀)
      let has_type_a' : Γ.toCtx ⊢ a.toTm ∶ A.toTm⌈⋆⌉₀ := by
        let h := has_type_a.down
        rewrite [toTm_subst] at h
        exact h
      let has_type_b ← has_type f Γ b .unit
      return ⟨A⌈ₐb⌉₀, (toTm_subst _ _) ▸ HasType.unit_elim is_type_A.down
        has_type_a' has_type_b.down⟩
    | f+1, Γ, .indEmpty A b => do
      let is_type_A ← is_type f _ (Γ ⬝a .empty) A
      let has_type_b ← has_type f Γ b .empty
      return ⟨A⌈ₐb⌉₀, (toTm_subst _ _) ▸ HasType.empty_elim is_type_A.down has_type_b.down⟩
    | f+1, Γ, .lam A b => do
      let ⟨B, h⟩ ← infer_type f (Γ ⬝a A) b
      return ⟨.pi A B, HasType.pi_intro h⟩
    | f+1, Γ, .app g a => do
      let ⟨.pi A B, hg⟩ ← infer_type f Γ g
        | .error s!"infer_type: expected a lambda term at {g.toTm}"
      let has_type_a ← has_type f Γ a A
      return ⟨B⌈ₐa⌉₀, (toTm_subst _ _) ▸ HasType.pi_elim hg has_type_a.down⟩
    | f+1, Γ, .pairSigma a b B => do
      let ⟨A, ha⟩ ← infer_type f Γ a
      let hb ← has_type f Γ b (B⌈ₐa⌉₀)
      let is_type_B ← is_type f _ (Γ ⬝a A) B
      return ⟨.sigma A B, HasType.sigma_intro ha ((toTm_subst _ _) ▸ hb.down) is_type_B.down⟩
    | f+1, Γ, .indSigma A B C c p => do
      let is_type_C ← is_type f _ (Γ ⬝a (.sigma A B)) C
      let has_type_c ← has_type f ((Γ ⬝a A) ⬝a B) c (C⌈ₐ(ₐₛ↑ₚ↑ₚidₚ)⋄ₐ
        .pairSigma (.var 1) (.var 0) (B⌊ₐ↑ₚ↑ₚidₚ⌋)⌉)
      let has_type_p ← has_type f Γ p (.sigma A B)
      return ⟨C⌈ₐp⌉₀, (toTm_subst _ _) ▸ HasType.sigma_elim is_type_C.down
        (by
          let h := has_type_c.down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_asubst] at h
          exact h)
        has_type_p.down⟩
    | f+1, Γ, .zeroNat => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return ⟨.nat, HasType.nat_zero_intro ctx_ok.down⟩
    | f+1, Γ, .succNat n => do
      let is_nat_n ← has_type f Γ n .nat
      return ⟨.nat, HasType.nat_succ_intro is_nat_n.down⟩
    | f+1, Γ, .indNat A z s n => do
      let is_type_A ← is_type f _ (Γ ⬝a .nat) A
      let has_type_z ← has_type f Γ z (A⌈ₐ.zeroNat⌉₀)
      let has_type_s ← has_type f ((Γ ⬝a .nat) ⬝a A) s (A⌈ₐ(ₐₛ↑ₚidₚ)⋄ₐ (.succNat (.var 0))⌉⌊ₐ↑ₚidₚ⌋)
      let has_type_n ← has_type f Γ n .nat
      return ⟨A⌈ₐn⌉₀, (toTm_subst _ _) ▸ HasType.nat_elim is_type_A.down
        ((toTm_subst _ .zeroNat) ▸ has_type_z.down)
        (by
          let h := has_type_s.down
          rewrite [toCtx_extend] at h
          rewrite [toCtx_extend] at h
          rewrite [toTm_weak] at h
          rewrite [toTm_asubst] at h
          exact h)
        has_type_n.down⟩
    | f+1, Γ, .refl A a => do
      let has_type_A ← is_type f _ Γ A
      let has_type_a ← has_type f Γ a A
      return ⟨.iden A a a, HasType.iden_intro has_type_A.down has_type_a.down⟩
    | f+1, Γ, .j A B b a₁ a₂ p => do
      let is_type_B ← is_type f _
        (((Γ ⬝a A) ⬝a (A⌊ₐ↑ₚidₚ⌋)) ⬝a ((A⌊ₐ↑ₚ↑ₚidₚ⌋).iden (.var 1) (.var 0))) B
      let has_type_b ← has_type f (Γ ⬝a A) b
        (B⌈ₐ(ₐₛidₚ)⋄ₐ (.var 0)⋄ₐ .refl (A⌊ₐ↑ₚidₚ⌋) (.var 0)⌉)
      let has_type_a₁ ← has_type f Γ a₁ A
      let has_type_a₂ ← has_type f Γ a₂ A
      let has_type_p ← has_type f Γ p (A.iden a₁ a₂)
      return ⟨B⌈ₐ(ₐₛidₚ)⋄ₐ a₁⋄ₐ a₂⋄ₐ p⌉,
        (toTm_asubst _ _) ▸ HasType.iden_elim
          (by
            let h := is_type_B.down
            rewrite [toCtx_extend] at h
            rewrite [toCtx_extend] at h
            rewrite [toCtx_extend] at h
            rewrite [toTm_weak] at h
            simp [ATm.toTm] at h
            rewrite [toTm_weak] at h
            exact h
            )
          (by
            let h := has_type_b.down
            rewrite [toCtx_extend] at h
            rewrite [toTm_asubst] at h
            simp [ASubst.toSubst, ATm.toTm] at h
            rewrite [toTm_weak] at h
            exact h)
          has_type_a₁.down has_type_a₂.down has_type_p.down⟩
    | _+1, _, t => .error s!"infer_type: unsupported pattern {t.toTm}"
  termination_by structural fuel
end
