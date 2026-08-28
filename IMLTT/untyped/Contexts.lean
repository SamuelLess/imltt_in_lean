import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

inductive CtxGen : Nat → Nat → Type where
  | start {n : Nat} : CtxGen n n
  | expand : CtxGen m n → Tm n → CtxGen m (n + 1)

def concat_ctx {l m n : Nat} (Γ : CtxGen l m) (Δ : CtxGen m n) : CtxGen l n :=
  match Δ with
  | .start => Γ
  | .expand Δ' T => (CtxGen.expand (concat_ctx Γ Δ') T)

def to_gen_ctx : Ctx m → CtxGen 0 m
  | .empty => CtxGen.start
  | .extend Γ' T => CtxGen.expand (to_gen_ctx Γ') T

def to_val_ctx : CtxGen 0 m → Ctx m
  | .start => ε
  | .expand Γ' T => (to_val_ctx Γ') ⬝ T

def expand_ctx (Γ : Ctx m) (Δ : CtxGen m n) : Ctx n :=
  match Δ with
  | .start => Γ
  | .expand Δ' T => Ctx.extend (expand_ctx Γ Δ') T

theorem gen_ctx_nil : CtxGen m 0 → m = 0 :=
  by
    intro Γ
    cases Γ
    case start =>
      rfl

theorem gen_ctx_leq : CtxGen m n → m ≤ n :=
  by
    intro Γ
    induction Γ
    case start =>
      omega
    case expand Δ' T ih =>
      omega

theorem gen_ctx_neq : CtxGen (m + 1) n → n ≠ 0 :=
  by
    intro Γ
    induction Γ
    case start =>
      omega
    case expand Δ' T ih =>
      omega

theorem gen_ctx_leq_sub : CtxGen (m + 1) n → m ≤ n - 1 :=
  by
    intro Γ
    induction Γ
    case start =>
      omega
    case expand Δ' T ih =>
      omega

theorem ht_ext_exp_n {n : Nat} {neq : n ≠ 0} : n = n - 1 + 1 := by omega
theorem ht_ext_exp_n_extr {n : Nat} {neq : n ≠ 0} : n + 1 - 1 = n - 1 + 1 := by omega

def substitute_into_gen_ctx
    (s : Tm l) (Δ : CtxGen (m + 1) n) (leq : l ≤ m) : CtxGen m (n - 1) :=
  match Δ with
  | .start => CtxGen.start
  | .expand (n:= n) Δ' T =>
    have h1 := gen_ctx_leq Δ'
    have h3 : n ≠ 0 := by apply gen_ctx_neq Δ'
    have h2 : l ≤ n - 1 := by omega
    ht_ext_exp_n_extr (neq := h3) ▸ (CtxGen.expand
      (substitute_into_gen_ctx s Δ' leq)
      ((ht_ext_exp_n (neq := h3) ▸ T)⌈s/ₙ h2⌉))

def substitute_shift_into_gen_ctx
    (s : Tm l) (Δ : CtxGen m n) (leq : l ≤ m) : CtxGen m n :=
  match Δ with
  | .start => CtxGen.start
  | .expand (n:= n) Δ' T =>
    have h :  m ≤ n := gen_ctx_leq Δ'
    have h1 : l ≤ n := by omega
    .expand (substitute_shift_into_gen_ctx s Δ' leq) (substitute (n_substitution_shift h1 s) T)

def weaken_from_into_gen_ctx (l : Nat) (Δ : CtxGen m n) : CtxGen (m + 1) (n + 1) :=
  match Δ with
  | .start => CtxGen.start
  | .expand (n := n') Δ' T =>
    .expand (weaken_from_into_gen_ctx l Δ') (T⌊(weaken_from n' l)⌋)

infixl:93 " ⊗ " => expand_ctx
infixl:94 " ⊙ " => CtxGen.expand

notation:95 "⌈" s "⌉(" Δ "w/" leq ")" => substitute_into_gen_ctx s Δ leq
notation:95 "⌈" s "↑⌉(" Δ "w/" leq ")" => substitute_shift_into_gen_ctx s Δ leq
notation:95 "⌊↑₁↬" l "⌋" Δ => weaken_from_into_gen_ctx l Δ
-- notation:95 "⌊⇑ₙ↑₁" l "⌋" Δ => weaken_from_into_gen_ctx l Δ






-- deprecated:

-- insert into context where all after *independent* of inserted type
def insert_into_ctx {l n : Nat} (leq : l ≤ n) (Γ : Ctx n) (S : Tm l) : Ctx (n + 1) :=
  match Γ with
  | .empty =>
    by
      simp [] at leq
      apply Ctx.extend ε (leq ▸ S)
  | .extend (n := n') Γ' T =>
    if h1 : l = n' + 1 then
      Γ' ⬝ T ⬝ (h1 ▸ S)
    else
      (insert_into_ctx (leq := by omega) Γ' S) ⬝ (T⌊weaken_from n' l⌋)

def get_sub_context (Γ : Ctx n) (l : Nat) (leq : l ≤ n) : Ctx l :=
  match n with
  | .zero =>
    match l with
    | .zero =>
      ε
    | .succ l' =>
      False.elim (by simp [] at leq)
  | .succ n' =>
    if h : l < n' + 1 then
      match Γ with
      | .extend Γ' T => get_sub_context (leq := by omega) Γ' l
    else
      have h : l = n' + 1 := by omega
      h ▸ Γ

theorem helper_get_type_context : n ≤ 0 → ¬(n = 0) → False := by omega

def remove_from_ctx (leq : l ≤ n) (Γ : Ctx (n + 1)) (s : Tm l) : Ctx n :=
  match Γ with
  | .extend Γ' T =>
    if h1 : l = n then
      Γ'
    else
      match n with
      | .zero =>
        False.elim (helper_get_type_context leq h1)
      | .succ n' =>
        (remove_from_ctx (leq := by omega) Γ' s) ⬝ (T⌈n_substitution (leq := by omega) s⌉)
  termination_by n

def get_from_context (Γ : Ctx (n + 1)) (l : Nat) (leq : l ≤ n) : Tm l :=
  match Γ with
  | .extend Γ' T =>
    if h1 : l = n then
      h1 ▸ T
    else
      match n with
      | .zero =>
        False.elim (helper_get_type_context leq h1)
      | .succ n' =>
        get_from_context (leq := by omega) Γ' l
