import IMLTT.typed.JudgmentsAndRules
import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

def fuel := 20 -- proof go brrr 🚗

def is_ctx : ((k : Nat) -> (Γsome : Ctx k) → (T : Tm k) → Option (PLift (Γsome ⊢ T type)))
    -> (Γ : Ctx n) -> Option (PLift (Γ ctx))
  | _, ε => pure <| .up IsCtx.empty
  | my_is_type, Ctx.extend Γ' T' => do
    let ctx_ok ← is_ctx my_is_type Γ'
    let t_ok : PLift (Γ' ⊢ T' type) ← my_is_type _ Γ' T'
    return .up <| IsCtx.extend ctx_ok.down t_ok.down

mutual
  def is_type : (fuel : Nat) -> (n : Nat)
      -> (Γ : Ctx n) → (T : Tm n) → Option (PLift (Γ ⊢ T type))
    | 0, _, _, _ => none
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

  def has_type : (fuel : Nat) -> (Γ : Ctx n) → (t : Tm n) → (T : Tm n) → Option (PLift (Γ ⊢ t ∶ T))
    | 0, _, _, _ => none
    | f+1, Γ, ⋆, 𝟙 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| HasType.unit_intro ctx_ok.down
    | f+1, Γ, 𝓏, 𝒩 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| HasType.nat_zero_intro ctx_ok.down
    | f+1, Γ, 𝓈(n), 𝒩 => do
      let has_type_n ← has_type f Γ n 𝒩
      return .up <| HasType.nat_succ_intro has_type_n.down
    | f+1, Γ, 𝟘, 𝒰 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| HasType.univ_empty ctx_ok.down
    | f+1, Γ, 𝟙, 𝒰 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| HasType.univ_unit ctx_ok.down
    | f+1, Γ, 𝒩, 𝒰 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      have : 1 = 1 := rfl
      return .up <| HasType.univ_nat ctx_ok.down
    -- more HasType.univ_* cases
    | _+1, ε, Tm.var _, T => none
    | f+1, Γ ⬝ T, v(⟨0,_⟩), T' =>  do
      let eq_type ← is_eq_type f (Γ ⬝ T) (T⌊↑ₚidₚ⌋) T'
      let is_type_T ← is_type f _ Γ T
      have has_type_T : (Γ ⬝ T) ⊢ v(0) ∶ (T⌊↑ₚidₚ⌋) := HasType.var is_type_T.down
      return .up <| HasType.ty_conv has_type_T eq_type.down
    | f+1, Γ ⬝ T, v(⟨i+1,_⟩), T' => do
      let ⟨T'', h⟩ ← infer_type f Γ v(.mk i (by simp_all only [Nat.add_lt_add_iff_right]))
      let is_type_T' ← is_type f _ Γ T''
      let is_type_T ← is_type f _ Γ T
      let weak := HasType.weak h is_type_T.down
      let eq_type ← is_eq_type f (Γ ⬝ T) (T''⌊↑ₚidₚ⌋) T'
      return .up <| HasType.ty_conv weak eq_type.down
    | f+1, Γ, λA;t, ΠA';B' => do
      let eq_type ← is_eq_type f Γ A A'
      let is_type_A ← is_type f _ Γ A
      let is_type_B' ← is_type f _ (Γ ⬝ A) B'
      let has_type_t ← has_type f (Γ ⬝ A) t B' -- v(0) is now bound by A
      let pi_intro := HasType.pi_intro has_type_t.down
      let pi_type := IsType.pi_form is_type_A.down is_type_B'.down
      let ⟨_, hB'type⟩ := pi_is_type_inversion pi_type
      let hB'rfl := defeq_refl_type hB'type
      let pi_eq : (Γ ⊢ ΠA;B' ≡ ΠA';B' type) := IsEqualType.pi_form_eq eq_type.down hB'rfl
      return .up <| HasType.ty_conv pi_intro pi_eq
    | f+1, Γ, a&b, ΣA;B => do
      let is_type_B ← is_type f _ (Γ ⬝ A) B
      let has_type_a ← has_type f Γ a A
      let has_type_b ← has_type f Γ b (B⌈a⌉₀)
      let sigma_intro := HasType.sigma_intro has_type_a.down has_type_b.down is_type_B.down
      return .up <| sigma_intro
    | f+1, Γ, (λA;t) ◃ a, B' => do
      let has_type_a ← has_type f Γ a A
      let ⟨B, _⟩ ← infer_type f (Γ ⬝ A) t
      let has_type_b : PLift (Γ ⬝ A ⊢ t ∶ B) ← has_type f (Γ ⬝ A) t B
      let pi_intro := HasType.pi_intro has_type_b.down
      let pi_elim : Γ ⊢ (λA;t)◃a ∶ B⌈a⌉₀ := HasType.pi_elim pi_intro has_type_a.down
      let conv_eq : PLift (Γ ⊢ B⌈a⌉₀ ≡ B' type) ← is_eq_type f Γ (B⌈a⌉₀) B'
      return .up <| HasType.ty_conv pi_elim conv_eq.down
    | _, _, _, _ => none
  termination_by structural f => f

  def is_eq_type : (fuel : Nat) -> (Γ : Ctx n) → (A : Tm n) → (B : Tm n) →
      Option (PLift (Γ ⊢ A ≡ B type))
    | 0, _, _, _ => none
    | f+1, Γ, 𝟙, 𝟙 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.unit_form_eq ctx_ok.down
    | f+1, Γ, 𝟘, 𝟘 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualType.empty_form_eq ctx_ok.down
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
      let eq_term <- is_eq_term f Γ A a₁ a₂
      let eq_term' <- is_eq_term f Γ A' a₃ a₄
      return .up <| IsEqualType.iden_form_eq eq_type_A.down eq_term.down eq_term'.down
    | _, _, _, _ => none
  termination_by structural f => f

  def is_eq_term : (fuel: Nat) -> (Γ : Ctx n) ->
      (A : Tm n) → (a : Tm n) → (a' : Tm n) → Option (PLift (Γ ⊢ a ≡ a' ∶ A))
    | 0, _, _, _, _ => none
    | f+1, Γ, 𝟙, ⋆, ⋆ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .up <| IsEqualTerm.unit_intro_eq ctx_ok.down
    | _, _, _, _, _ => none
  termination_by structural f => f

  def infer_type : (fuel : Nat) → (Γ : Ctx n) → (t : Tm n) → Option (Σ' T, Γ ⊢ t ∶ T)
    | 0, _, _ => none
    | f+1, Γ, ⋆ => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .mk 𝟙 <| HasType.unit_intro ctx_ok.down
    | f+1, Γ, 𝓏 => do
      let ctx_ok ← is_ctx (is_type f) Γ
      return .mk 𝒩 <| HasType.nat_zero_intro ctx_ok.down
    | f+1, Γ, 𝓈(n) => do
      let ctx_ok ← is_ctx (is_type f) Γ
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
    /-| f+1, Γ ⬝ T, v(⟨(i+1), _⟩) => do
      let ⟨T', h⟩ ← infer_type f Γ v(.mk i (by simp_all only [Nat.add_lt_add_iff_right]))
      let is_type_T' ← is_type f _ Γ T'
      let is_type_T ← is_type f _ Γ T
      return .mk (T'⌊↑ₚidₚ⌋) <| HasType.weak h is_type_T.down-/
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
    /-| f+1, Γ, (λA;b) ◃ a => do
      let has_type_a ← has_type f Γ a A
      let ⟨B, hb⟩ ← infer_type f (Γ ⬝ A) b
      return .mk (B⌈a⌉₀) <| HasType.pi_elim (HasType.pi_intro hb) has_type_a.down-/
    | f+1, Γ, g ◃ a => do
      let ⟨ΠA;B, hg⟩ ← infer_type f Γ g
        | failure
      let has_type_a ← has_type f Γ a A
      return .mk (B⌈a⌉₀) <| HasType.pi_elim hg has_type_a.down
    | f+1, _, _ => none
  termination_by structural f => f
end


--example : (ε ⊢ a ∶ A) → (ε ⊢ b ∶ B'a') → (ε ⬝ A ⊢ b) := by sorry

example {α : Type} {β : α -> Type} {x : α} {f : α → β x} : (a : α) × β a :=
  Sigma.mk x (f x)

example : (a : Nat) × (Vector Nat a) :=
  have s := Sigma.mk 3 (Vector.replicate 3 3)
  s

set_option pp.proofs true

#reduce (has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) v(1) 𝒩)
--#reduce (infer_type fuel (ε ⬝ 𝟘 ⬝ 𝒩 ⬝ 𝟙) v(2))
#reduce (has_type fuel (ε ⬝ 𝟘 ⬝ 𝒩 ⬝ 𝟙) v(2) 𝟘)

#reduce (has_type fuel ε ((λ𝒰; v(0))◃𝟙) 𝒰)

#reduce (is_eq_type fuel (ε ⬝ 𝟙) 𝟙 (𝟙⌊↑ₚidₚ⌋⌈v(0)⌉₀))


theorem star_unit : ε ⊢ ⋆ ∶ 𝟙 := ((has_type 1 ε ⋆ 𝟙).get (by native_decide)).down

#reduce has_type fuel ε (Tm.lam 𝒩 v(0)) (Tm.pi 𝒩 𝒩)

theorem idpi : ε ⊢ Tm.lam 𝒩 v(0) ∶ Tm.pi 𝒩 𝒩 :=
  ((has_type fuel ε (Tm.lam 𝒩 v(0)) (Tm.pi 𝒩 𝒩)).get (by native_decide)).down

#reduce has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0)))◃v(1)) 𝒩

#reduce has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0))&v(0))◃v(1)) (Σ𝒩;𝒩)

def ret_id : Tm n := (λ𝒰;(λv(0);v(0)))

#reduce has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0))&((ret_id◃𝒩)◃v(0)))◃v(1)) (Σ𝒩;𝒩)

#reduce has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0))&((λ𝒰;(λv(0);v(0))◃𝒩)◃v(0)))◃v(1)) (Σ𝒩;𝒩)
#reduce has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) ((λ𝒩;𝓈(v(0))&((λ𝒰;(λv(0);v(0))◃𝒩)◃v(0)))◃v(1)) (Σ𝒩;𝒩)
#reduce has_type fuel (ε ⬝ 𝒩 ⬝ 𝟙) (((λ𝒰;(λv(0);v(0)))◃𝒩)◃v(1)) 𝒩
#reduce has_type fuel (ε ⬝ 𝒩) ((λ𝒩;v(0))◃v(0)) 𝒩
#reduce has_type fuel (ε ⬝ 𝒩) (((λ𝒰;v(0)))◃𝒩) 𝒰
#reduce has_type fuel (ε ⬝ 𝒩) ((λ(((λ𝒰;v(0)))◃𝒩);v(0))◃v(0)) 𝒩

#reduce is_eq_type fuel (ε ⬝ 𝒩) (((λ𝒰;v(0)))◃𝒩) 𝒩

/-
theorem istype : ε ⊢ (λ𝟙;𝟙) ◃ ⋆ type :=
  ((is_type fuel 0 ε ((λ𝟙;𝟙) ◃ ⋆)).get (by native_decide)).down
-/
example : ε ⊢ (Tm.lam 𝒩 𝓈(v(0))) ∶ Tm.pi 𝒩 𝒩 :=
  ((has_type fuel ε (Tm.lam 𝒩 𝓈(v(0))) (Tm.pi 𝒩 𝒩)).get (by native_decide)).down
