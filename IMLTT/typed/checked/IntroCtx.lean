import IMLTT.typed.checked.Elaboration

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

theorem intro_ctx_type (Γ : Ctx n) :
    (ε ⊢ T type) → (Γ ctx) → (Γ ⊢  T⌊shift n⌋ type) := by
  intro hεTtype hΓctx
  induction Γ with
  | empty => simpa
  | @extend n' Γ' A ih =>
    have hsuccn : shift (n' + 1) = (↑ₚshift n') := rfl
    rw [hsuccn, ←weakening_shift_id]
    exact weakening_type (ih (ctx_decr hΓctx)) (ctx_extr hΓctx)

theorem intro_ctx {Γ : Ctx n} :
    (ε ⊢ t ∶ T) → (Γ ctx) → (Γ ⊢ (t⌊shift n⌋) ∶ T⌊shift n⌋) := by
  intro htT hΓctx
  induction Γ with
  | empty => simpa
  | @extend n' Γ' A ih =>
    have : shift (n' + 1) = (↑ₚshift n') := rfl
    rw [this, ←weakening_shift_id]
    rw (occs := [2]) [←weakening_shift_id]
    exact weakening_term (ih (ctx_decr hΓctx)) (ctx_extr hΓctx)
