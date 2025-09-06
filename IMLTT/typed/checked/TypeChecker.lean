import IMLTT.typed.JudgmentsAndRules
import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

def fuel := 200 -- proof go brrr 🚗

def is_ctx : ((k : Nat) -> (Γsome : Ctx k) → (T : Tm k) → Except String (PLift (Γsome ⊢ T type)))
    -> (Γ : Ctx n) -> Except String (PLift (Γ ctx))
  | _, ε => pure <| .up IsCtx.empty
  | my_is_type, Ctx.extend Γ' T' => do
    let ctx_ok ← is_ctx my_is_type Γ'
    let t_ok : PLift (Γ' ⊢ T' type) ← my_is_type _ Γ' T'
    return .up <| IsCtx.extend ctx_ok.down t_ok.down

mutual
  def is_type : (fuel : Nat) -> (n : Nat)
      -> (Γ : Ctx n) → (T : Tm n) → Except String (PLift (Γ ⊢ T type))
    | 0, _, _, _ => .error "is_type: out of fuel"
    | f+1, _, Γ, 𝟘 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsType.empty_form ctx_ok.down
    | f+1, _, Γ, 𝟙 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsType.unit_form ctx_ok.down
    | f+1, _, Γ, 𝒩 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsType.nat_form ctx_ok.down
    | f+1, _, Γ, 𝒰 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsType.univ_form ctx_ok.down
    | f+1, _, Γ, ΠA;B => do
      let is_type_A ← is_type f _ Γ A
      let is_type_B ← is_type f _ (Γ ⬝ A) B
      return .up <| IsType.pi_form is_type_A.down is_type_B.down
    | f+1, _, Γ, ΣA;B => do
      let is_type_A ← is_type f _ Γ A
      let is_type_B ← is_type f _ (Γ ⬝ A) B
      return .up <| IsType.sigma_form is_type_A.down is_type_B.down
    | f+1, _, Γ, a ≃[A] a' => do
      let is_type_A ← is_type f _ Γ A
      let has_type_a ← has_type f Γ a A
      let has_type_a' ← has_type f Γ a' A
      return .up <| IsType.iden_form is_type_A.down has_type_a.down has_type_a'.down
    | f+1, _, Γ, A => do
      let has_type_A ← has_type f Γ A 𝒰
      return .up <| IsType.univ_elim has_type_A.down
  termination_by structural f => f

  def has_type : (fuel : Nat) → (Γ : Ctx n) →
      (t : Tm n) → (T : Tm n) → Except String (PLift (Γ ⊢ t ∶ T))
    | 0, _, _, _ => .error "has_type: out of fuel"
    -- variables
    | _+1, ε, v(i), T => .error s!"has_type: can't have v({i}) in empty context"
    | f+1, Γ ⬝ T, v(⟨0,_⟩), T' =>  do
      let is_type_T ← is_type f _ Γ T
      let is_eq_type_T_T' ← is_eq_type f (Γ ⬝ T) (T⌊↑ₚidₚ⌋) T'
      have has_type_T : (Γ ⬝ T) ⊢ v(0) ∶ (T⌊↑ₚidₚ⌋) := HasType.var is_type_T.down
      return .up <| HasType.ty_conv has_type_T is_eq_type_T_T'.down
    | f+1, Γ ⬝ T, v(⟨i+1,_⟩), T' => do
      let ⟨T'', h⟩ ← infer_type f Γ v(.mk i (by omega))
      let is_type_T ← is_type f _ Γ T
      let is_eq_type_T ← is_eq_type f (Γ ⬝ T) (T''⌊↑ₚidₚ⌋) T'
      let weak := HasType.weak h is_type_T.down
      return .up <| HasType.ty_conv weak is_eq_type_T.down
    -- intro rules
    | f+1, Γ, ⋆, Unit => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type ← is_eq_type f Γ 𝟙 Unit
      return .up <| HasType.ty_conv (HasType.unit_intro ctx_ok.down) is_eq_type.down
    | f+1, Γ, 𝓏, N => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type ← is_eq_type f Γ 𝒩 N
      return .up <| HasType.ty_conv (HasType.nat_zero_intro ctx_ok.down) is_eq_type.down
    | f+1, Γ, 𝓈(n), N => do
      let has_type_n ← has_type f Γ n 𝒩
      let is_eq_type_N ← is_eq_type f Γ 𝒩 N
      return .up <| HasType.ty_conv (HasType.nat_succ_intro has_type_n.down) is_eq_type_N.down
    | f+1, Γ, λA;t, P => do
      let ⟨ΠA';B', hp⟩ ← infer_type f Γ (λA;t)
        | .error s!"has_type: expected Π-type at {λA;t}, instead got {P}"
      let has_type_t ← has_type f (Γ ⬝ A) t B' -- v(0) is now bound by A
      let pi_intro := HasType.pi_intro has_type_t.down
      let is_eq_type_P ← is_eq_type f Γ (ΠA;B') P
      return .up <| HasType.ty_conv pi_intro is_eq_type_P.down
    | f+1, Γ, a&b, ΣA;B => do -- can't use infer_type here because of dependent types
      let is_type_B ← is_type f _ (Γ ⬝ A) B
      let has_type_a ← has_type f Γ a A
      let has_type_b ← has_type f Γ b (B⌈a⌉₀)
      return .up <| HasType.sigma_intro has_type_a.down has_type_b.down is_type_B.down
    | f+1, Γ, Tm.refl A a, a' ≃[A'] a'' => do
      let is_type_A ← is_type f _ Γ A
      let has_type_a ← has_type f Γ a A
      have t : Γ ⊢ A.refl a ∶ a' ≃[A'] a'' := by
        apply HasType.ty_conv (B:=a' ≃[A'] a'')
        apply HasType.iden_intro is_type_A.down has_type_a.down
        apply IsEqualType.iden_form_eq
        · exact (← is_eq_type f Γ A A').down
        · exact (← is_eq_term f Γ a a' A).down
        · exact (← is_eq_term f Γ a a'' A').down
      return .up <| t
    -- univ intro rules
    | f+1, Γ, 𝟘, Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ 𝒰 Univ
      return .up <| HasType.ty_conv (HasType.univ_empty ctx_ok.down) is_eq_type_U.down
    | f+1, Γ, 𝟙, Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ 𝒰 Univ
      return .up <| HasType.ty_conv (HasType.univ_unit ctx_ok.down) is_eq_type_U.down
    | f+1, Γ, 𝒩, Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ 𝒰 Univ
      return .up <| HasType.ty_conv (HasType.univ_nat ctx_ok.down) is_eq_type_U.down
    | f+1, Γ, ΠA;B , Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ 𝒰 Univ
      let has_type_A_U ← has_type f Γ A 𝒰
      let has_type_B_U ← has_type f (Γ ⬝ A) B 𝒰
      return .up <| HasType.ty_conv
        (HasType.univ_pi has_type_A_U.down has_type_B_U.down) is_eq_type_U.down
    | f+1, Γ, ΣA;B , Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ 𝒰 Univ
      let has_type_A_U ← has_type f Γ A 𝒰
      let has_type_B_U ← has_type f (Γ ⬝ A) B 𝒰
      return .up <| HasType.ty_conv
        (HasType.univ_sigma has_type_A_U.down has_type_B_U.down) is_eq_type_U.down
    | f+1, Γ, a ≃[A] a' , Univ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      let is_eq_type_U ← is_eq_type f Γ 𝒰 Univ
      let has_type_A_U ← has_type f Γ A 𝒰
      let has_type_a_A ← has_type f Γ a A
      let has_type_a'_A ← has_type f Γ a' A
      return .up <| HasType.ty_conv
        (HasType.univ_iden has_type_A_U.down has_type_a_A.down has_type_a'_A.down) is_eq_type_U.down
    -- elim rules
    | f+1, Γ, .indEmpty A a, B => do
      return .up <| by
        apply HasType.ty_conv (B:=B)
        apply HasType.empty_elim
        · exact (← is_type f _ (Γ ⬝ 𝟘) A).down
        · exact (← has_type f Γ a 𝟘).down
        · exact (← is_eq_type f Γ (A⌈a⌉₀) B).down
    | f+1, Γ, .indUnit A b a, B => do
      return .up <| by
        apply HasType.ty_conv (B:=B)
        apply HasType.unit_elim
        · exact (← is_type f _ (Γ ⬝ 𝟙) A).down
        · exact (← has_type f Γ a (A⌈⋆⌉₀)).down
        · exact (← has_type f Γ b 𝟙).down
        · exact (← is_eq_type f Γ (A⌈b⌉₀) B).down
    | f+1, Γ, g ◃ a, B' => do
      let ⟨ΠA;B, hg⟩ ← infer_type f Γ g
        | .error s!"has_type: expected lambda term at {g}"
      let has_type_a ← has_type f Γ a A
      have pi_elim := HasType.pi_elim hg has_type_a.down
      let is_eq_type_B ← is_eq_type f Γ (B⌈a⌉₀) B'
      return .up <| HasType.ty_conv pi_elim is_eq_type_B.down
    | f+1, Γ, .indSigma A B C c p, C' => do
      return .up <| by
        apply HasType.ty_conv (B:=C')
        apply HasType.sigma_elim
        · exact (← is_type f _ (Γ ⬝ ΣA;B) C).down
        · exact (← has_type f (Γ ⬝ A ⬝ B) c (C⌈(ₛ↑ₚ↑ₚidₚ)⋄ v(1)&v(0)⌉)).down
        · exact (← has_type f Γ p (ΣA;B)).down
        · exact (← is_eq_type f Γ (C⌈p⌉₀) C').down
    | f+1, Γ, .indNat A z s n, A' => do
      return .up <| by
        apply HasType.ty_conv (B:=A')
        apply HasType.nat_elim
        · exact (← is_type f _ (Γ ⬝ 𝒩) A).down
        · exact (← has_type f Γ z (A⌈𝓏⌉₀)).down
        · exact (← has_type f (Γ ⬝ 𝒩 ⬝ A) s (A⌈(ₛ↑ₚidₚ)⋄ 𝓈(v(0))⌉⌊↑ₚidₚ⌋)).down
        · exact (← has_type f Γ n 𝒩).down
        · exact (← is_eq_type f Γ (A⌈n⌉₀) A').down
    | f+1, Γ, .j A B b a a' p, B' => do
      return .up <| by
        apply HasType.ty_conv (B:=B')
        apply HasType.iden_elim
        · exact (← is_type f _ (Γ ⬝ A ⬝ A⌊↑ₚidₚ⌋ ⬝ v(1) ≃[A⌊↑ₚ↑ₚidₚ⌋] v(0)) B).down
        · exact (← has_type f (Γ ⬝ A) b (B⌈(ₛidₚ)⋄ v(0)⋄ .refl (A⌊↑ₚidₚ⌋) v(0)⌉)).down
        · exact (← has_type f Γ a A).down
        · exact (← has_type f Γ a' A).down
        · exact (← has_type f Γ p (a ≃[A] a')).down
        · exact (← is_eq_type f Γ (B⌈(ₛidₚ)⋄ a⋄ a'⋄ p⌉) B').down
    | _, _, t, T => .error s!"has_type: unsupported pattern {t} ∶ {T}"
  termination_by structural f => f

  def is_eq_type : (fuel : Nat) -> (Γ : Ctx n) → (A : Tm n) → (B : Tm n) →
      Except String (PLift (Γ ⊢ A ≡ B type))
    | 0, _, A, B => .error s!"is_eq_type: out of fuel {A} ≡ {B}"
    -- congruence (formation) rules
    | f+1, Γ, 𝟘, 𝟘 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.empty_form_eq ctx_ok.down
    | f+1, Γ, 𝟙, 𝟙 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.unit_form_eq ctx_ok.down
    | f+1, Γ, 𝒩, 𝒩 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.nat_form_eq ctx_ok.down
    | f+1, Γ, 𝒰, 𝒰 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.univ_form_eq ctx_ok.down
    | f+1, Γ, ΠA;B, ΠA';B' => do
      let eq_type_A ← is_eq_type f (Γ) A A'
      let eq_type_B ← is_eq_type f (Γ ⬝ A) B B'
      return .up <| IsEqualType.pi_form_eq eq_type_A.down eq_type_B.down
    | f+1, Γ, ΣA;B, ΣA';B' => do
      let eq_type_A ← is_eq_type f (Γ) A A'
      let eq_type_B ← is_eq_type f (Γ ⬝ A) B B'
      return .up <| IsEqualType.sigma_form_eq eq_type_A.down eq_type_B.down
    | f+1, Γ, a₁ ≃[A] a₃, a₂ ≃[A'] a₄ => do
      let eq_type_A ← is_eq_type f Γ A A'
      let eq_term <- is_eq_term f Γ a₁ a₂ A
      let eq_term' <- is_eq_term f Γ a₃ a₄ A'
      return .up <| IsEqualType.iden_form_eq eq_type_A.down eq_term.down eq_term'.down
    -- TODO: check if more patterns are needed here
    | f+1, Γ ⬝ T, v(i), T' => do
      let ⟨𝒰, _⟩ ← infer_type f (Γ ⬝ T) v(i)
        | .error s!"is_eq_type: expected 𝒰 at v({i})"
      let eq_term_in_𝒰 ← is_eq_term f (Γ ⬝ T) v(i) T' 𝒰
      return .up <| IsEqualType.univ_elim_eq eq_term_in_𝒰.down
    | f+1, Γ, g◃x, T => do
      let eq_term_in_𝒰 ← is_eq_term f Γ (g◃x) T 𝒰
      return .up <| IsEqualType.univ_elim_eq eq_term_in_𝒰.down
    | f+1, Γ, T, T' => do
      let is_eq_symm ← is_eq_type f Γ T' T
      return .up <| IsEqualType.type_symm is_eq_symm.down
    --| _, _, A, B => .error s!"is_eq_type: unsupported pattern for either side {A} ≡ {B}"
  termination_by structural f => f

  def is_eq_term : (fuel: Nat) -> (Γ : Ctx n) ->
      (a : Tm n) → (a' : Tm n) → (A : Tm n) → Except String (PLift (Γ ⊢ a ≡ a' ∶ A))
    | 0, Γ, a, a', A =>
      .error s!"is_eq_term: out of fule with {repr Γ} ⊢ {a} ≡ {a'} : {A}"
    -- variables
    | f+1, Γ ⬝ T, v(0), v(0), T' => do
      let is_type_T ← is_type f _ Γ T
      let is_eq_T_T' ← is_eq_type f (Γ ⬝ T) (T⌊↑ₚidₚ⌋) T'
      have := IsEqualTerm.var_eq is_type_T.down
      return .up <| IsEqualTerm.ty_conv_eq this is_eq_T_T'.down
    | f+1, Γ ⬝ T, v(⟨i+1,hi⟩), v(⟨j+1,hj⟩), T' => do
      if hieqj : i == j then
        let ⟨Tvi, htvi⟩ ← infer_type f Γ v(⟨i, by omega⟩)
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
        .error s!"is_eq_term: two different variables cannot defeq v({i}) ≡ v({j}) ∶ {T'}"
    -- computation rules
    -- TODO: unit_comp
    | f+1, Γ, (λA;b)◃x, t, T => do
      let ⟨Π_;B, _⟩ ← infer_type f Γ (λA;b)
        | .error s!"is_eq_term: could not infer type of {λA;b}"
      let has_type_x ← has_type f Γ x A
      let has_type_b ← has_type f (Γ ⬝ A) b B
      have pi_comp := IsEqualTerm.pi_comp has_type_b.down has_type_x.down
      let is_eq_term_b ← is_eq_term f Γ (b⌈x⌉₀) t (B⌈x⌉₀)
      let is_eq_type_B_T ← is_eq_type f Γ (B⌈x⌉₀) T
      have := IsEqualTerm.term_trans pi_comp is_eq_term_b.down
      return .up <| IsEqualTerm.ty_conv_eq this is_eq_type_B_T.down
    -- TODO: sigma_comp
    -- TODO: nat_zero_comp
    -- TODO: nat_succ_comp
    -- TODO: iden_comp
    -- congruence rules
    | f+1, Γ, ⋆, ⋆, 𝟙 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.unit_intro_eq ctx_ok.down
    -- TODO: unit_elim_eq
    -- TODO: empty_elim_eq
    -- TODO: pi_intro_eq
    -- TODO: pi_elim_eq
    -- TODO: sigma_intro_eq
    -- TODO: sigma_elim_eq
    -- TODO: nat_zero_intro_eq
    -- TODO: nat_succ_intro_eq
    -- TODO: nat_elim_eq
    -- TODO: iden_intro_eq
    -- TODO: iden_elim_eq
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
          is_eq_term_A_A'.down is_eq_term_a₁_a₃.down is_eq_term_a₂_a₄.down) is_eq_type_U_Univ.down
    -- conversion
    | f+1, Γ, a, a', A => do
      let is_eq_symm ← is_eq_term f Γ a' a A
      return .up <| IsEqualTerm.term_symm is_eq_symm.down
  termination_by structural f => f

  def infer_type : (fuel : Nat) → (Γ : Ctx n) → (t : Tm n) → Except String (Σ' T, Γ ⊢ t ∶ T)
    | 0, _, _ => .error "infer_type: out of fuel"
    | f+1, Γ, ⋆ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .mk 𝟙 <| HasType.unit_intro ctx_ok.down
    | f+1, Γ, 𝓏 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .mk 𝒩 <| HasType.nat_zero_intro ctx_ok.down
    | f+1, Γ, 𝓈(n) => do
      let is_nat_n ← has_type f Γ n 𝒩
      return .mk 𝒩 <| HasType.nat_succ_intro is_nat_n.down
    | f+1, Γ, 𝟙 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .mk 𝒰 <| HasType.univ_unit ctx_ok.down
    | f+1, Γ, 𝒩 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .mk 𝒰 <| HasType.univ_nat ctx_ok.down
    | f+1, Γ ⬝ T, v(0) => do
      let is_type_T ← is_type f _ Γ T
      return .mk (T⌊↑ₚidₚ⌋) <| HasType.var is_type_T.down
    | f+1, Γ ⬝ T, v(⟨(i+1), _⟩) => do
      let ⟨T', h⟩ ← infer_type f Γ v(.mk i (by simp_all only [Nat.add_lt_add_iff_right]))
      let is_type_T ← is_type f _ Γ T
      return .mk (T'⌊↑ₚidₚ⌋) <| HasType.weak h is_type_T.down
    | f+1, Γ, λA;b => do
      let ⟨B, h⟩ ← infer_type f (Γ ⬝ A) b
      return .mk (Tm.pi A B) <| HasType.pi_intro h
    | f+1, Γ, a&b => do
      -- FIXME: this does not work for proper dependent pairs
      let ⟨A, ha⟩ ← infer_type f Γ a
      let ⟨Bsubsta, hb⟩ ← infer_type f Γ b
      let B := Bsubsta⌊↑ₚidₚ⌋
      let is_equal_type_B_B' ← is_eq_type f Γ Bsubsta (B⌈a⌉₀)
      let is_type_B ← is_type f _ (Γ ⬝ A) B
      have := HasType.ty_conv hb is_equal_type_B_B'.down
      return .mk (ΣA;B) <| HasType.sigma_intro ha this is_type_B.down
    --| f+1, Γ, a◃b => do
    | f+1, Γ, g ◃ a => do
      let ⟨ΠA;B, hg⟩ ← infer_type f Γ g
        | .error s!"infer_type: expected a lambda term at {g}"
      let has_type_a ← has_type f Γ a A
      return .mk (B⌈a⌉₀) <| HasType.pi_elim hg has_type_a.down
    | f+1, _, t => .error s!"infer_type: unsupported pattern {t}"
  termination_by structural f => f
end

set_option pp.proofs true

instance : ToString (Except String (PLift α)) where
  toString e := match e with
    | .error s => s
    | .ok _ => "success"

#eval has_type fuel (ε ⬝ 𝒰 ⬝ 𝒰 ⬝ Σv(1);v(1)) (v(2).indSigma v(1) v(2 + 1) v(0 + 1) v(0)) v(1)
#eval is_ctx (is_type fuel) (ε ⬝ 𝒰 ⬝ 𝒰 ⬝ Σv(1);v(1))

#eval is_eq_term fuel (ε ⬝ 𝟙) (v(0)⌈⋆⌉₀) (⋆)  𝟙

#eval is_ctx (is_type fuel) (ε ⬝ 𝒰 ⬝ 𝟙 ⬝ (v(2)⌈⋆⌉₀))

/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝟙 ⬝ 𝟙 ⬝ (λ𝟙; 𝒩)◃v(0)⌈⋆⌉₀) v(0) ((λ𝟙; 𝒩)◃v(0)⌈⋆⌉₀)


/-- info: success -/
#guard_msgs in
#eval is_ctx (is_type fuel) (ε ⬝ 𝟙 ⬝ 𝒰 ⬝ 𝒩 ⬝ (v(2)⌈⋆⌉₀))
--(ε ⬝ 𝟙 ⬝ 𝒰 ⬝ 𝒩 ⬝ (v(3)⌈⋆⌉₀) ⊢ indUnit v(2) v(3) v(0) ∶ v(2)⌈v(3)⌉₀)

/-- info: success -/
#guard_msgs in
#eval has_type fuel ((ε ⬝ 𝒰 ⬝ 𝒰 ⬝ 𝒰 ⬝ Πv(1);v(1)) ⬝ Πv(3);v(3))
  ((λΠv(3);v(3); λΠv(5);v(5); λv(6); v(2)◃(v(1)◃v(0)))◃v(1)◃v(0)) (Πv(4);v(3))

/-- info: success -/
#guard_msgs in
#eval (has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) v(1) 𝒩)
/-- info: success -/
#guard_msgs in
#eval (has_type fuel (ε ⬝ 𝟘 ⬝ 𝒩 ⬝ 𝟙) v(2) 𝟘)
/-- info: success -/
#guard_msgs in
#eval (has_type fuel ε ((λ𝒰; v(0))◃𝟙) 𝒰)
/-- info: success -/
#guard_msgs in
#eval (is_eq_type fuel (ε ⬝ 𝟙) 𝟙 (𝟙⌊↑ₚidₚ⌋⌈v(0)⌉₀))

theorem star_unit : ε ⊢ ⋆ ∶ 𝟙 := ((has_type fuel ε ⋆ 𝟙).toOption.get (by native_decide)).down

/-- info: success -/
#guard_msgs in
#eval has_type fuel ε (Tm.lam 𝒩 v(0)) (Tm.pi 𝒩 𝒩)

theorem idpi : ε ⊢ Tm.lam 𝒩 v(0) ∶ Tm.pi 𝒩 𝒩 :=
  ((has_type fuel ε (Tm.lam 𝒩 v(0)) (Tm.pi 𝒩 𝒩)).toOption.get (by native_decide)).down

/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0)))◃v(1)) 𝒩

/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0))&v(0))◃v(1)) (Σ𝒩;𝒩)

def ret_id : Tm n := (λ𝒰;(λv(0);v(0)))

/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0))&((ret_id◃𝒩)◃v(0)))◃v(1)) (Σ𝒩;𝒩)

/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0))&((λ𝒰;((λv(0);v(0))))◃𝒩◃v(0)))◃v(1)) (Σ𝒩;𝒩)

/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) (((λ𝒰;(λv(0);v(0)))◃𝒩)◃v(1)) 𝒩

/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒩) ((λ𝒩;v(0))◃v(0)) 𝒩
/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒩) (((λ𝒰;v(0)))◃𝒩) 𝒰
/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒩) ((λ(((λ𝒰;v(0)))◃𝒩);v(0))◃v(0)) 𝒩

/-- info: success -/
#guard_msgs in
#eval is_eq_type fuel (ε ⬝ 𝒰) v(0) v(0)

/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒰) (((λ𝒰;(λv(0);v(0)))◃𝒩)◃𝓏) 𝒩
/-- info: success -/
#guard_msgs in
#eval has_type fuel (ε ⬝ 𝒰 ⬝ (Πv(0);v(1)) ⬝ v(1)) ((v(1) ◃ v(0))) v(2)



/-- info: success -/
#guard_msgs in
#eval is_eq_type fuel (ε ⬝ 𝒩) (((λ𝒰;v(0)))◃𝒩) 𝒩

example : ε ⊢ (Tm.lam 𝒩 𝓈(v(0))) ∶ Tm.pi 𝒩 𝒩 :=
  ((has_type fuel ε (Tm.lam 𝒩 𝓈(v(0))) (Tm.pi 𝒩 𝒩)).toOption.get (by native_decide)).down
