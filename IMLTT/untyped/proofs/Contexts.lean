import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Contexts
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution

import Aesop

@[simp]
theorem empty_expand_context {n : Nat} {Γ : Ctx n} :
    Γ ⊗ CtxGen.start = Γ :=
  by
    rfl

theorem extend_expand_context_simp {Γ : Ctx l} {Δ : CtxGen (l) n} {A : Tm n}:
    Γ ⊗ (Δ ⊙ A) =
    (Γ ⊗ Δ) ⬝ A :=
  by
    rfl

theorem extend_expand_context {Γ : Ctx l} {Δ : CtxGen (l) n} {A : Tm n}:
    (Γ ⊗ Δ) ⬝ A =
    Γ ⊗ (Δ ⊙ A) :=
  by
    rfl

@[simp]
theorem middle_expand_context :
    Γ ⊗ CtxGen.start ⊙ A ⊙ B = Γ ⬝ A ⊗ CtxGen.start ⊙ B :=
  by
    rfl

theorem context_to_gen_ctx :
    Γ ⬝ A = Γ ⊗ CtxGen.start ⊙ A :=
  by
    rfl

theorem context_shift_gen_ctx :
    Γ ⬝ S ⊗ Δ = Γ ⊗ (concat_ctx (.start ⊙ S) Δ) :=
  by
    induction Δ with
    | start =>
      rfl
    | expand Δ' S' ih =>
      simp [expand_ctx]
      rw [ih]
      rfl

@[simp]
theorem empty_extend_expand_context_n_substitution {n : Nat} {Γ : Ctx n} {s : Tm n} :
    Γ ⊗ ⌈s⌉(CtxGen.start w/ (Nat.le_refl n)) =
    Γ ⊗ CtxGen.start :=
  by
    rfl

@[simp]
theorem extend_expand_context_n_substitution' {Γ : Ctx l} {Δ : CtxGen (l + 1) (n + 1)} {A : Tm (n + 1)}:
    (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⬝ (A)⌈s/ₙ(gen_ctx_leq_sub Δ)⌉ =
    Γ ⊗ ⌈s⌉((Δ ⊙ A) w/Nat.le_refl l) :=
  by
    rfl

@[simp]
theorem extend_expand_context_n_substitution_simp {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A : Tm n}:
    ht_ext_exp_n_extr (neq := gen_ctx_neq Δ) ▸ Γ ⊗ ⌈s⌉((Δ ⊙ A) w/Nat.le_refl l) =
    (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⬝ (ht_ext_exp_n (neq := gen_ctx_neq Δ) ▸ A)⌈s/ₙ(gen_ctx_leq_sub Δ)⌉ :=
  by
    simp []
    induction Δ
    case start =>
      rfl
    case expand Δ T =>
      simp


theorem extend_expand_context_n_substitution {Γ : Ctx l} {Δ : CtxGen (l + 1) (n)} {A : Tm n}:
    (Γ ⊗ ⌈s⌉(Δ w/Nat.le_refl l)) ⬝ (ht_ext_exp_n (neq := gen_ctx_neq Δ) ▸ A)⌈s/ₙ(gen_ctx_leq_sub Δ)⌉ =
    ht_ext_exp_n_extr (neq := gen_ctx_neq Δ) ▸ Γ ⊗ ⌈s⌉((Δ ⊙ A) w/Nat.le_refl l) :=
  by
    simp []

@[simp]
theorem empty_extend_expand_context_n_substitution_shift {n : Nat} {Γ : Ctx n} {s : Tm n} :
    Γ ⊗ ⌈s↑⌉(CtxGen.start w/ (Nat.le_refl n)) =
    Γ ⊗ CtxGen.start :=
  by
    rfl

@[simp]
theorem extend_expand_context_n_substitution_shift_simp {Γ : Ctx l} {Δ : CtxGen (l) (n)} {A : Tm n}:
    Γ ⊗ ⌈s↑⌉((Δ ⊙ A) w/Nat.le_refl l) =
    (Γ ⊗ ⌈s↑⌉(Δ w/Nat.le_refl l)) ⬝ A⌈s↑/ₙ(gen_ctx_leq Δ)⌉ :=
  by
    rfl

theorem extend_expand_context_n_substitution_shift {Γ : Ctx l} {Δ : CtxGen (l) (n)} {A : Tm n}:
    (Γ ⊗ ⌈s↑⌉(Δ w/Nat.le_refl l)) ⬝ A⌈s↑/ₙ(gen_ctx_leq Δ)⌉ =
    Γ ⊗ ⌈s↑⌉((Δ ⊙ A) w/Nat.le_refl l) :=
  by
    rfl

@[simp]
theorem empty_expand_context_weaken_from {n : Nat} {Γ : Ctx n} {S : Tm n} :
    (Γ ⬝ S ⊗ (⌊↑₁↬l⌋CtxGen.start))
    = Γ ⬝ S ⊗ (CtxGen.start) :=
  by
    rw [weaken_from_into_gen_ctx]

@[simp]
theorem extend_expand_context_weaken_from_simp {Γ : Ctx l} {Δ : CtxGen (l) (n)} {S : Tm l} {A : Tm n}:
    Γ ⬝ S ⊗ (⌊↑₁↬l⌋(Δ ⊙ A))
    = (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⬝ A⌊↑₁n↬l⌋ :=
  by
    rfl

theorem extend_expand_context_weaken_from {Γ : Ctx l} {Δ : CtxGen (l) (n)} {S : Tm l} {A : Tm n}:
    (Γ ⬝ S ⊗ (⌊↑₁↬l⌋Δ)) ⬝ A⌊↑₁n↬l⌋
    = Γ ⬝ S ⊗ (⌊↑₁↬l⌋(Δ ⊙ A)) :=
  by
    rfl


theorem extend_start_expand_context :
    Γ ⬝ S ⊗ Δ =
    Γ ⊗ (concat_ctx (.start ⊙ S) Δ) :=
  by
    induction Δ with
    | start =>
      simp [concat_ctx]
      simp [expand_ctx]
    | expand Δ' S' ih =>
      simp [concat_ctx]
      simp [expand_ctx]
      apply ih

theorem extend_start_expand_context_weaken_from {Γ : Ctx l} {Δ : CtxGen (l + 1) n} {S : Tm l}:
    (Γ ⬝ S ⊗ ⌊↑₁↬l⌋(concat_ctx (CtxGen.start ⊙ S) Δ)) =
    (Γ ⬝ S ⬝ S⌊↑₁l↬l⌋ ⊗ ⌊↑₁↬l⌋Δ) :=
  by
    induction Δ with
    | start =>
      simp [concat_ctx]
    | expand Δ' S' ih =>
      simp [concat_ctx]
      rw [ih]
      rfl




-- DEPRECATED:

theorem empty_insert_into_context :
    insert_into_ctx (leq := Nat.le_refl 0) ε B = ε ⬝ B :=
  by
    aesop

theorem head_insert_into_context {n : Nat} {Γ : Ctx n} {B : Tm n} :
    Γ ⬝ B = insert_into_ctx (leq := Nat.le_refl n) Γ B :=
  by
    cases Γ with
    | empty =>
      apply empty_insert_into_context
    | extend Γ' t =>
      simp [insert_into_ctx]

theorem middle_insert_into_context {n : Nat} {Γ : Ctx n} {A S : Tm n} :
    Γ ⬝ S ⬝ A⌊↑ₚidₚ⌋ = insert_into_ctx (leq := Nat.le_succ n) (Γ ⬝ A) S :=
  by
    simp [insert_into_ctx]
    rw [head_insert_into_context]
    simp [weaken_from_zero]

theorem extend_insert_into_context {leq : l ≤ n} {Γ : Ctx n} :
    insert_into_ctx (leq := leq) Γ S ⬝ A⌊weaken_from n l⌋ = insert_into_ctx (leq := Nat.le_succ_of_le leq) (Γ ⬝ A) S :=
  by
    cases n with
    | zero =>
      cases l with
      | zero =>
        simp [insert_into_ctx]
      | succ l' =>
        simp [insert_into_ctx]
        apply False.elim
        omega
    | succ n' =>
      simp only [insert_into_ctx]
      split
      · simp
        apply And.intro
        · apply False.elim
          omega
        · apply False.elim
          omega
      · case isFalse h1 =>
        simp [weaken_from]

theorem empty_get_sub_context {leq : l = 0} :
    get_sub_context (leq := Nat.le_of_eq leq) ε l = leq ▸ ε :=
  by
    aesop

theorem extend_get_sub_context {leq : l <= n} {Γ : Ctx n} :
    get_sub_context (leq := Nat.le_succ_of_le leq) (Γ ⬝ A) l = get_sub_context (leq := leq) Γ l :=
  by
    simp [get_sub_context]
    split
    case isTrue h =>
      rfl
    case isFalse h =>
      omega

theorem head_get_sub_context {eq : l = n} {Γ : Ctx n} :
    get_sub_context (leq := Nat.le_of_eq eq) Γ l = eq ▸ Γ :=
  by
    cases n with
    | zero =>
      cases l with
      | zero =>
        simp [get_sub_context]
        cases Γ with
        | empty =>
          rfl
      | succ l' =>
        omega
    | succ n' =>
      cases l with
      | zero =>
        omega
      | succ l' =>
        simp [get_sub_context]
        split
        case succ.succ.isTrue hT =>
          omega
        case succ.succ.isFalse hF =>
          rfl

theorem head_get_from_context {eq : l = n} {Γ : Ctx n} :
    get_from_context (leq := Nat.le_of_eq eq) (Γ ⬝ A) l = eq ▸ A :=
  by
    simp [get_from_context]
    split
    case isTrue h =>
      rfl
    case isFalse h =>
      omega

theorem extend_get_from_context {leq : l <= n} {Γ : Ctx (n + 1)} :
    get_from_context (leq := Nat.le_succ_of_le leq) (Γ ⬝ A) l = get_from_context (leq := leq) Γ l :=
  by
    simp [get_from_context]
    split
    case isTrue h =>
      omega
    case isFalse h =>
      rfl

theorem head_remove_from_context {eq : l = n} {Γ : Ctx n} :
    remove_from_ctx (l := l) (leq := Nat.le_of_eq eq) (Γ ⬝ A) s = Γ :=
  by
    simp [remove_from_ctx]
    omega

theorem extend_remove_from_context {leq : l ≤ n} {Γ : Ctx (n + 1)} {s : Tm l}:
    remove_from_ctx (leq := leq) Γ s ⬝ A⌈n_substitution (leq := leq) s⌉ = remove_from_ctx (leq := Nat.le_succ_of_le leq) (Γ ⬝ A) s :=
  by
    simp [remove_from_ctx]
    omega
