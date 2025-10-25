import IMLTT.typed.checked.Elaboration

theorem unitcontextunit : ε ⬝ 𝟙 ⊢ v(0) ∶ 𝟙 := HasType.var (IsType.unit_form IsCtx.empty)

example : ε ⬝ 𝒩 ⬝ 𝟙 ⊢ v(0) ∶ 𝟙 := HasType.var
  (IsType.unit_form (IsCtx.extend IsCtx.empty (IsType.nat_form IsCtx.empty)))


example : ε ⬝ 𝒩 ⬝ 𝟙 ⊢ v(1) ∶ 𝒩 := by
  let Γ := ε ⬝ 𝒩
  have : Γ ctx := IsCtx.extend IsCtx.empty (IsType.nat_form IsCtx.empty)
  have hΓ1 : Γ ⊢ 𝟙 type := IsType.unit_form this
  have hwo : Γ ⊢ v(0) ∶ 𝒩 := HasType.var (IsType.nat_form IsCtx.empty)
  exact HasType.weak hwo hΓ1

example : ε ⬝ 𝟙 ⊢ (.refl 𝟙 v(0)) ∶ v(0) ≃[𝟙] v(0) := by
  let Γ := ε ⬝ 𝟙
  have hΓctx : Γ ctx := IsCtx.extend IsCtx.empty (IsType.unit_form IsCtx.empty)
  have hΓ1type : Γ ⊢ 𝟙 type := IsType.unit_form hΓctx
  have : Γ ⊢ v(0) ∶ 𝟙 := HasType.var (IsType.unit_form IsCtx.empty)
  exact HasType.iden_intro hΓ1type this

example (Γ : Ctx n) : (Γ ⊢ A type) -> (Γ ⬝ A ⊢ v(0) ∶ shift_tm A) := by
  intro hAtype
  apply HasType.var
  exact hAtype

example (Γ : Ctx n) : ∀ a : Tm n, (Γ ⊢ a ∶ 𝒩) → (Γ ⬝ 𝒩 ⊢ (shift_tm a) ≃[𝒩] v(0) type) := by
  intro a ha
  apply IsType.iden_form
  · apply IsType.nat_form
    apply IsCtx.extend
    exact boundary_ctx_term ha
    apply IsType.nat_form (boundary_ctx_term ha)
  · have hΓNtype := IsType.nat_form (boundary_ctx_term ha)
    exact weakening_term ha hΓNtype
  · apply HasType.var
    apply IsType.nat_form
    exact boundary_ctx_term ha

example (Γ : Ctx n) : ∀ a : Tm n, (Γ ⊢ a ∶ A) → (Γ ⬝ A ⊢ a⌊↑ₚidₚ⌋ ≃[A⌊↑ₚidₚ⌋] v(0) type) := by
  intro a ha
  have hae : Γ ⬝ A ⊢ a⌊↑ₚidₚ⌋ ∶ A⌊↑ₚidₚ⌋ := by
    apply weakening_term
    exact ha
    exact boundary_term_type ha
  apply IsType.iden_form
  · exact boundary_term_type hae
  · exact hae
  · apply HasType.var
    exact boundary_term_type ha


theorem idpi'' : (Γ ctx) -> Γ ⊢ Tm.lam 𝒩 v(0) ∶ Tm.pi 𝒩 𝒩 := by
  intro hΓctx
  apply HasType.pi_intro
  apply HasType.var
  apply IsType.nat_form
  exact hΓctx

example : (Γ ctx) -> Γ ⊢ Tm.app (Tm.lam 𝒩 v(0)) 𝓏 ∶ 𝒩 := fun hΓctx ↦
  have h_pi := HasType.pi_intro (HasType.var (IsType.nat_form hΓctx));
  HasType.pi_elim h_pi (HasType.nat_zero_intro hΓctx)

example : (Γ ctx) -> Γ ⊢ (λ𝒩;v(0)) ◃ 𝓏 ∶ 𝒩 := by
  intro hΓctx
  have : Γ ⊢ λ𝒩;v(0) ∶ Π𝒩;𝒩 := by
    apply HasType.pi_intro
    apply HasType.var
    apply IsType.nat_form
    exact hΓctx
  apply HasType.pi_elim this
  exact HasType.nat_zero_intro hΓctx

example : weaken ρ (.lam A b) =
    .lam (weaken ρ A) (weaken (lift_weak_n 1 ρ) b) := rfl

@[simp]
def shift : (n : Nat) -> Weak n 0
  | 0 => Weak.id
  | n + 1 => Weak.shift <| shift n

example : Tm n :=
  let t : Tm 0 := Tm.tt
  (t⌊shift n⌋)

theorem weaken_from_n : (↑₁n↬n) = ↑ₚidₚ := by
  unfold weaken_from
  split <;> simp

theorem intro_ctx_type {n : Nat} (Γ : Ctx n) :
    (Γ ctx) -> (ε ⊢ T type) → (Γ ⊢  T⌊shift n⌋ type) := by
  intro hΓctx hεTtype
  induction Γ with
  | empty => simpa
  | @extend n' Γ' A ih =>
    have hΓ'ctx : Γ' ctx := ctx_decr hΓctx
    have hΓ'Atype : Γ' ⊢ A type := ctx_extr hΓctx
    have hsuccn : shift (n' + 1) = (↑ₚshift n') := rfl
    rw [hsuccn, ←weakening_shift_id]
    exact weakening_type (ih hΓ'ctx) hΓ'Atype

theorem intro_ctx (Γ : Ctx n) :
    (Γ ctx) -> (ε ⊢ t ∶ T) → (Γ ⊢ (t⌊shift n⌋) ∶ T⌊shift n⌋) := by
  intro hΓctx htT
  induction Γ with
  | empty => simpa
  | @extend n' Γ' A ih =>
    have hΓ'ctx : Γ' ctx := ctx_decr hΓctx
    have hΓ'Atype : Γ' ⊢ A type := ctx_extr hΓctx
    have : shift (n' + 1) = (↑ₚshift n') := rfl
    rw [this, ←weakening_shift_id]
    rw (occs := [2]) [←weakening_shift_id]
    exact weakening_term (ih hΓ'ctx) hΓ'Atype

theorem var_as_type : (Γ ctx) → (Γ ⬝ U ⊢ v(0) type) → (Γ ⬝ U ⬝ v(0) ⊢ v(0) ∶ v(1)) := by
  intro hΓctx hv0type
  apply HasType.var
  exact hv0type

theorem var_univ_type : ε ⬝ 𝒰 ⊢ v(0) type := by
  apply boundary_type_eq_type' (A := v(0))
  apply IsEqualType.univ_elim_eq
  apply IsEqualTerm.var_eq
  apply IsType.univ_form
  exact IsCtx.empty

theorem var_type : ε ⬝ 𝒰 ⬝ v(0) ⊢ v(0) ∶ v(1) := by
  apply HasType.var
  apply boundary_type_eq_type' (A := v(0))
  apply IsEqualType.univ_elim_eq
  apply IsEqualTerm.var_eq
  apply IsType.univ_form
  exact IsCtx.empty

theorem var_type_univ : ε ⬝ 𝒰  ⊢ v(0) type := by
  apply boundary_type_eq_type' (A := v(0))
  apply IsEqualType.univ_elim_eq
  apply IsEqualTerm.var_eq
  apply IsType.univ_form
  exact IsCtx.empty

--#imltt ε ⬝ (A : 𝒰) ⬝ (IdA : Π(a : A; A)) ⬝ (a : A) ⊢ (IdA a) : A
theorem var_type' : ε ⬝ 𝒰 ⬝ (Πv(0);v(1)) ⬝ v(1) ⊢ v(1)◃v(0) ∶ v(2) := by
  let Γ := ε ⬝ 𝒰 ⬝ (Πv(0);v(1)) ⬝ v(1)
  have : ε ⬝ 𝒰 ⬝ (Πv(0);v(1)) ⬝ v(1) ⊢ v(1) ∶ (Πv(0+2);v(1+2)) := by
    --apply HasType.weak
    apply HasType.weak (B:= v(1)) (Γ := ε ⬝ 𝒰 ⬝ (Πv(0);v(1))) (i := 0) (A := (Πv(1);v(2)))
    · apply HasType.var (A := Πv(0);v(1))
      refine IsType.pi_form ?_ ?_
      · exact var_type_univ
      · apply boundary_type_eq_type' (A := v(1))
        apply IsEqualType.univ_elim_eq
        apply IsEqualTerm.weak_eq (B := v(0)) (Γ := ε ⬝ 𝒰) (i := 0) (A := 𝒰)
        · aesop
        · exact var_type_univ
    · apply boundary_type_eq_type' (A := v(1))
      apply IsEqualType.univ_elim_eq
      apply IsEqualTerm.weak_eq (B := Πv(0);v(1)) (Γ := ε ⬝ 𝒰) (i := 0) (A := 𝒰)
      · aesop
      · refine IsType.univ_elim ?_
        apply HasType.univ_pi
        · aesop
        · apply HasType.weak (B := v(0)) (Γ := ε ⬝ 𝒰) (i := 0) (A := 𝒰)
          · aesop
          · aesop
  apply HasType.pi_elim this
  apply HasType.var
  apply boundary_type_eq_type' (A := v(1))
  apply IsEqualType.univ_elim_eq
  apply IsEqualTerm.weak_eq (i := 0) (B := Πv(0);v(1)) (Γ := ε ⬝ 𝒰) (A := 𝒰)
  · aesop
  · refine IsType.univ_elim ?_
    apply HasType.univ_pi
    · aesop
    · apply HasType.weak (B := v(0)) (Γ := ε ⬝ 𝒰) (i := 0) (A := 𝒰)
      · aesop
      · aesop

-- redundancy of rules
example (hctx : Γ ctx) : Γ ⊢ 𝟙 ≡ 𝟙 type :=
  IsEqualType.unit_form_eq hctx
example (hctx : Γ ctx) : Γ ⊢ 𝟙 ≡ 𝟙 type :=
  IsEqualType.univ_elim_eq <| IsEqualTerm.univ_unit_eq hctx
