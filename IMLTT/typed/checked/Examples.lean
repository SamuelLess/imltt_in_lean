import IMLTT.typed.JudgmentsAndRules
import IMLTT.untyped.AbstractSyntax
import IMLTT.typed.proofs.admissable.Weakening
import IMLTT.typed.proofs.boundary.BoundaryTypesTerms

open Tm

-- Unit type and terms
#check 𝟙
#check ⋆
#check indUnit (v(0)) (v(1)) (v(2))

-- Empty type
#check 𝟘
#check indEmpty (v(0)) (v(1))

-- Pi types and lambda abstraction
#check Π 𝟙; v(0)
#check λ 𝟙; v(0)
#check (λ 𝟙; v(0)) ◃ ⋆

-- Sigma types and pairs
#check Σ 𝟙; v(0)
#check ⋆ & ⋆
#check indSigma (v(0)) (v(1)) (v(2)) (v(3)) (v(4))

-- Natural numbers
#check 𝒩
#check 𝓏
#check 𝓈(𝓏)
#check indNat (v(0)) (v(1)) (v(2)) (v(3))

-- Identity types
#check ⋆ ≃[𝟙] ⋆
#check refl 𝟙 ⋆
#check j (v(0)) (v(1)) (v(2)) (v(3)) (v(4)) (v(5))

-- Universe
#check 𝒰

-- Context examples
#check ε ⬝ 𝟙 ⬝ v(0)
#reduce ε ⬝ 𝟙 ⬝ 𝒩 ⬝ (v(0) ≃[𝒩] v(1))
#reduce ε ⬝ (Π 𝟙; v(0)) ⬝ (λ 𝟙; v(0))

-- More complex examples
#check λ (Σ 𝟙; v(0)); v(0) & v(1)
#check indNat (Π 𝒩; v(0)) 𝓏 (λ 𝒩; λ v(0); 𝓈(v(1))) (𝓈(𝓈(𝓏)))
#check j (v(0) ≃[v(1)] v(2)) (v(3)) (v(4)) (v(5)) (refl v(6) v(7)) (v(8))


-- First, define addition as a recursive function
def add : Tm n :=
  λ 𝒩; λ 𝒩; indNat (Π 𝒩; v(0))
    (λ 𝒩; v(0))                     -- base case: 0 + m = m
    (λ 𝒩; λ 𝒩; λ v(0); 𝓈(v(1)))     -- step case: (succ n) + m = succ (n + m)
    (v(1))                           -- applied to first argumente

#check add ◃ 𝓏 ◃ (𝓈(𝓈(𝓏))) -- 0 + 2 = 2
#reduce add ◃ 𝓏 ◃ (𝓈(𝓈(𝓏))) -- 0 + 2 = 2

def zero_add_two : Tm 0 :=
  refl 𝒩 (add ◃ 𝓏 ◃ 𝓈(𝓈(𝓏)))  -- 0 + 2 ≃[𝒩] 2

def refl_zero : Tm 0 :=
  refl 𝒩 zeroNat

#check (Π 𝒩; (v(0) ≃[𝒩] (add◃v(0)◃𝓏)) : Tm 1)

example: ε ctx := IsCtx.empty

theorem unitcontextunit : ε ⬝ 𝟙 ⊢ v(0) ∶ 𝟙 := HasType.var (IsType.unit_form IsCtx.empty)

example : ε ⬝ 𝒩 ⬝ 𝟙 ⊢ v(0) ∶ 𝟙 := HasType.var
  (IsType.unit_form (IsCtx.extend IsCtx.empty (IsType.nat_form IsCtx.empty)))

/-
| weak :
  HasType Γ v(i) A → IsType Γ B
  → HasType (Γ ⬝ B) v(i.succ) (A⌊↑ₚidₚ⌋) -- XXX: change (v(i)⌊↑ₚidₚ⌋) to v(i.succ)? -> yes
-/

example : ε ⬝ 𝒩 ⬝ 𝟙 ⊢ v(1) ∶ 𝒩 := by
  let Γ := ε ⬝ 𝒩
  have : Γ ctx := IsCtx.extend IsCtx.empty (IsType.nat_form IsCtx.empty)
  have hΓ1 : Γ ⊢ 𝟙 type := IsType.unit_form this
  have hwo : Γ ⊢ v(0) ∶ 𝒩 := HasType.var (IsType.nat_form IsCtx.empty)
  exact HasType.weak hwo hΓ1

example : ε ⬝ 𝟙 ⊢ (refl 𝟙 v(0)) ∶ v(0) ≃[𝟙] v(0) := by
  let Γ := ε ⬝ 𝟙
  have hΓctx : Γ ctx := IsCtx.extend IsCtx.empty (IsType.unit_form IsCtx.empty)
  have hΓ1type : Γ ⊢ 𝟙 type := IsType.unit_form hΓctx
  have : Γ ⊢ v(0) ∶ 𝟙 := HasType.var (IsType.unit_form IsCtx.empty)
  exact HasType.iden_intro hΓ1type this

def add' : Tm n :=
  λ 𝒩; λ 𝒩; indNat (Π 𝒩; v(0))
    (λ 𝒩; v(0))                     -- base case: 0 + m = m
    (λ 𝒩; λ 𝒩; λ v(0); 𝓈(v(1)))     -- step case: (succ n) + m = succ (n + m)
    (v(1))                           -- applied to first argument

def add_zero : Tm n :=
  λ 𝒩;  -- ∀n : ℕ (n = v(0) in this scope)
  indNat (v(0) ≃[𝒩] (add ◃ v(0) ◃ 𝓏))  -- Motive P(n) = n + 0 = n
    (refl 𝒩 𝓏)  -- Base case: 0 + 0 = 0
    (λ 𝒩;  -- k = v(1), outer n = v(2)
      λ (v(0) ≃[𝒩] v(1));  -- ih : k + 0 = k (v(0) is ih, v(1) is k)
      j v(2)  -- A = 𝒩 (from outer scope)
        (λ 𝒩; λ 𝒩; λ 𝒩; 𝓈(v(1)) ≃[𝒩] 𝓈(v(2)))  -- Motive C
        (λ 𝒩; λ 𝒩; refl 𝒩 (𝓈(v(0))))  -- Refl case
        v(0)  -- p : k + 0 = k (ih)
        (add ◃ v(1) ◃ 𝓏)  -- x = k + 0
        v(1)  -- y = k
        --v(0)  -- p : k + 0 = k (ih again)
    )
    v(0)  -- Apply to input n (v(0) in outer scope)

example : ε ⬝ 𝒩 ⊢
  indNat (v(0) ≃[𝒩] (add ◃ v(0) ◃ 𝓏))  -- Motive P(n) = n + 0 = n
    (refl 𝒩 𝓏)  -- Base case: 0 + 0 = 0
    (λ 𝒩;  -- k = v(1), outer n = v(2)
      λ (v(0) ≃[𝒩] v(1));  -- ih : k + 0 = k (v(0) is ih, v(1) is k)
      j v(2)  -- A = 𝒩 (from outer scope)
        (λ 𝒩; λ 𝒩; λ 𝒩; 𝓈(v(1)) ≃[𝒩] 𝓈(v(2)))  -- Motive C
        (λ 𝒩; λ 𝒩; refl 𝒩 (𝓈(v(0))))  -- Refl case
        v(0)  -- p : k + 0 = k (ih)
        (add ◃ v(1) ◃ 𝓏)  -- x = k + 0
        v(1)  -- y = k
        --v(0)  -- p : k + 0 = k (ih again)
    ) v(0)
  ∶ (v(0) ≃[𝒩] (add◃v(0)◃𝓏))  := by
  simp [add_zero]
  sorry

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


theorem idpi : (Γ ctx) -> Γ ⊢ Tm.lam 𝒩 v(0) ∶ Tm.pi 𝒩 𝒩 := by
  intro hΓctx
  apply HasType.pi_intro
  apply HasType.var
  apply IsType.nat_form
  exact hΓctx

example : ε ⊢ Tm.app (Tm.lam 𝒩 𝓈(v(0))) 𝓏 ∶ 𝒩 := by
  have : ε ⊢ (Tm.lam 𝒩 𝓈(v(0))) ∶ Tm.pi 𝒩 𝒩 := by sorry
  apply HasType.pi_elim this
  exact HasType.nat_zero_intro IsCtx.empty

example : (Γ ctx) -> Γ ⊢ Tm.app (Tm.lam 𝒩 v(0)) 𝓏 ∶ 𝒩 := by
  intro hΓctx
  have : Γ ⊢ (Tm.lam 𝒩 v(0)) ∶ Tm.pi 𝒩 𝒩 := by
    apply HasType.pi_intro
    apply HasType.var
    apply IsType.nat_form
    exact hΓctx
  apply HasType.pi_elim this
  exact HasType.nat_zero_intro hΓctx

example : (Γ ctx) -> Γ ⬝ 𝒩 ⊢ Tm.app (Tm.lam 𝒩 𝓈(v(0))) v(0) ∶ 𝒩 := by
  intro hΓctx
  have : Γ ⬝ 𝒩 ⊢ (Tm.lam 𝒩 𝓈(v(0))) ∶ Tm.pi 𝒩 𝒩 := by sorry
  apply HasType.pi_elim this
  apply HasType.var
  apply IsType.nat_form
  exact hΓctx

example : weaken ρ (.lam A b) =
    .lam (weaken ρ A) (weaken (lift_weak_n 1 ρ) b) := rfl

def swap_args : (a -> b -> c) -> (b -> a -> c) := by exact fun a_1 a_2 a ↦ a_1 a a_2

def swap (F : Tm n) (A : Tm (n+1)) (B : Tm (n+1)) : Tm n := λF;λB;λ(A⌊↑ₚidₚ⌋);v(2)◃v(0)◃v(1)

example {A : Tm n} {B : Tm n} (hAtype : Γ ⊢ A type) (hBtype : Γ ⊢ B type)
    (hCtype : Γ ⬝ A ⬝ B⌊↑ₚidₚ⌋ ⊢ C type) :
    Γ ⊢ swap (ΠA;(Π(B⌊↑ₚidₚ⌋);C)) (A⌊↑ₚidₚ⌋) (B⌊↑ₚidₚ⌋) ∶
      Tm.pi (@Tm.pi n A (Tm.pi (B⌊↑ₚidₚ⌋) C)) (@Tm.pi (n+1) (B⌊↑ₚidₚ⌋) (Tm.pi (A⌊↑ₚidₚ⌋) C⌊↑ₚidₚ⌋)) := by
  simp
  rw [swap]
  apply HasType.pi_intro
  apply HasType.pi_intro
  simp
  apply HasType.pi_intro
  sorry
  --apply @HasType.pi_elim (n+3) ((Γ ⬝ ΠA;ΠB⌊↑ₚidₚ⌋;C) ⬝ B⌊↑ₚidₚ⌋ ⬝ A⌊↑ₚ↑ₚidₚ⌋) (v(2)◃v(0)) (v(1)) (C⌊⇑ₚ↑ₚ↑ₚidₚ⌋) (v(1))
  --apply @HasType.pi_intro (n+2) ((Γ ⬝ ΠA;ΠB⌊↑ₚidₚ⌋;C) ⬝ B⌊↑ₚidₚ⌋) (A⌊↑ₚ↑ₚidₚ⌋) (v(2)◃v(0)◃v(1)) (C⌊⇑ₚ↑ₚidₚ⌋)
  --apply @HasType.pi_intro (n+1) (Γ ⬝ ΠA;ΠB⌊↑ₚidₚ⌋;C) (A⌊↑ₚidₚ⌋) (λB⌊↑ₚ↑ₚidₚ⌋; v(2)◃v(1)◃v(0))



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
    (Γ ctx) -> (ε ⊢ T type) -> (Γ ⊢  T⌊shift n⌋ type) := by
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
    (Γ ctx) -> (ε ⊢ t ∶ T) -> (Γ ⊢ (t⌊shift n⌋) ∶ T⌊shift n⌋) := by
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
