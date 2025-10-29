import IMLTT.typed.checked.Elaboration
import IMLTT.typed.checked.IntroCtx

ttheorem star_unit : ε ⊢ ⋆ : 𝟙
ttheorem star_unit_app : ε ⊢ (λ(x : 𝟙). ⋆) ◃ ⋆ : 𝟙
theorem star_unit' : (Γ ctx) → (Γ ⊢ (λ𝟙;⋆) ◃ ⋆ ∶ 𝟙) := intro_ctx star_unit_app

def my_id := [atm| λ (T : 𝒰). λ (x : T) . x]

ttheorem app_my_id : ε ⬝ (T : 𝒰) ⬝ (x : T) ⊢ ((my_id ◃ T) ◃ x) : T

/-- error: Unknown identifier `my_typo`, context: my_type -/
#guard_msgs in
ttheorem own_type : ε ⬝ (my_type : 𝒰) ⊢ my_typo : 𝒰

/-- error: Type error: has_type: expected lambda term at v(0) -/
#guard_msgs in
ttheorem tc_fail : ε ⬝ (f : 𝒩) ⊢ f ◃ ⋆ : 𝟙

def myunit := [atm| 𝟙]

ttheorem wisunit : ε ⬝ (x : 𝟙) ⬝ (y : 𝒰) ⬝ (w : myunit) ⊢ w : 𝟙

ttheorem myid : ε ⬝ (A : 𝒰) ⬝ (IdA : Π(a : A; A)) ⬝ (a : A) ⊢ IdA ◃ a : A

def starp := [atm| (⋆ & ⋆):: 𝟙]

ttheorem starpair : ε ⊢ (⋆ & ⋆)::𝟙 : Σ(x : 𝟙; 𝟙)

def ret_id := [atm| (λ(T : 𝒰). λ (x : T). x)]

ttheorem retid : ε ⬝ (T : 𝒰) ⬝ (x : T) ⊢ (ret_id ◃ T) ◃ x : T

def natpair : ATm 0 := [atm|((λ (n:𝒩).
    (𝓈(n) & (ret_id ◃ 𝒩) ◃ 𝓏) :: 𝒩) ◃ 𝓏)]

ttheorem usingnextterm : ε  ⊢ natpair : Σ(x : 𝒩;𝒩)

def type_id := [atm| Π(T : 𝒰;Π (x : T;T))]

ttheorem emptyctx : ε ctx

theorem bridge : IsCtx ε := emptyctx

ttheorem id_is_type : ε ⊢ type_id type

ttheorem typeid1 : ε ⊢ ret_id : type_id
ttheorem typeid2 : ε ⊢ type_id ≡ Π(T : 𝒰;Π (x : T;T)) type
ttheorem typeid3 : ε ⊢ ret_id ≡ ret_id : type_id

ttheorem univ_var_type : ε ⬝ (A : 𝒰) ⊢ A type

theorem univ_var_type' :
    IsType (Ctx.extend Ctx.empty .univ) (.var 0) := by
  apply IsType.univ_elim
  apply HasType.var
  apply IsType.univ_form
  exact IsCtx.empty

theorem univ_var_type'' :
    IsType (Ctx.extend Ctx.empty .univ) (.var 0) := by aesop

theorem univ_var_type_atm :
    IsType (ACtx.extend Lean.Name.anonymous ACtx.empty .univ).toCtx (ATm.var 0).toTm := by
  exact ((is_type 5 _ _ _).toOption.get (by native_decide)).down

example : ε ⊢ 𝟙 ≡ 𝟙 type := IsEqualType.unit_form_eq IsCtx.empty
example : ε ⊢ 𝟙 ≡ 𝟙 type :=
  IsEqualType.univ_elim_eq <| IsEqualTerm.univ_unit_eq IsCtx.empty

ttheorem type_rfl : ε ⬝ (A : 𝒰) ⊢ A ≡ A type
ttheorem elem_rlf : ε ⬝ (A : 𝒰) ⬝ (a : A) ⊢ a ≡ a : A

ttheorem fun_ext : ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (f : A → B) ⊢ λ(a : A). (f ◃ a) : A → B

ttheorem star_eq : ε ⊢ ((λ (a : 𝟙). a))◃ ⋆ ≡ ⋆ : 𝟙
ttheorem star_eq' : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) ≡ ⋆ : 𝟙
ttheorem star_ty : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) : 𝟙
ttheorem unit_eq : ε ⊢ ((λ (A : 𝒰). A) ◃ 𝟙) ≡ 𝟙 : 𝒰

example (h : Γ ⊢ (t⌈ₐa⌉₀).toTm ∶ T) :
    (Γ ⊢ t.toTm⌈a.toTm⌉₀ ∶ T) := toTm_subst .. ▸ h

ttheorem pi_type : ε ⬝ (s : 𝟙) ⊢ (λ(x : 𝟙). s) : 𝟙 → 𝟙

ttheorem comp : ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⊢
  λ(g : B → C). λ(f : A → B). λ(x : A). g◃f◃x :
    (B → C) → (A → B) → (A → C)

theorem comp_tm : ε ⬝ 𝒰 ⬝ 𝒰 ⬝ 𝒰 ⊢ λΠv(1);v(1);λΠv(3);v(3);λv(4);v(2)◃(v(1)◃v(0)) ∶
  ΠΠv(1);v(1);ΠΠv(3);v(3);Πv(4);v(3) := by
  have := comp
  simp_all [ATm.toTm, ACtx.toCtx]

/-- error: Type error: is_type: out of fuel -/
#guard_msgs in
ttheorem comp_applied : ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⬝ (g' : B → C) ⬝ (f' : A → B) ⊢
    ((λ(g : B → C) . (λ(f : A → B) . (λ(x : A) . g ◃ (f ◃ x)))) ◃ g')  ◃ f' : A → C

instance : ToString (Except String (α)) where
  toString e := match e with
    | .error s => s
    | .ok _ => "success"

#guard_msgs(drop info) in
#eval normalize_type 50 [acx|ε] [atm|(Π(T:𝒰;T))]
#guard_msgs(drop info) in
#eval has_type 50 [acx|ε] [atm|(Π(T:𝒰;T))] [atm|𝒰] -- would prove unsoundness
#guard_msgs(drop info) in
#eval is_eq_type 30 [acx|ε] [atm|𝟙] [atm|(λ(T:𝒰).T) ◃ 𝟙]
#guard_msgs(drop info) in
#eval is_eq_type 50 [acx|ε] [atm|𝒰] [atm|𝒰]
#guard_msgs(drop info) in
#eval normalize 50 [acx|ε] [atm|(λ(T:𝒰). T) ◃ 𝟙] [atm| 𝒰]
#guard_msgs(drop info) in
#eval normalize 50 [acx|ε] [atm|(λ (x : 𝟙). x )] [atm|𝟙→𝟙]
#guard_msgs(drop info) in
#eval normalize 50 [acx|ε] [atm|((λ (T : 𝒰). (λ (x : T). x )) ◃ 𝟙) ◃ ⋆] [atm|𝟙]

ttheorem use_normalize : ε ⊢ ⋆ ≡ ((λ (T : 𝒰). (λ (x : T). x )) ◃ 𝟙) ◃ ⋆ : 𝟙
ttheorem use_normalize_type : ε ⊢ (λ(T:𝒰). T) ◃ 𝟙 ≡ (λ(U:𝒰). (λ(T:𝒰). T) ◃ 𝟙) ◃ 𝟙 type

example : (Γ ctx) -> Γ ⊢ (λ𝒩;v(0)) ◃ 𝓏 ∶ 𝒩 := by
  intro hΓctx
  have : Γ ⊢ λ𝒩;v(0) ∶ Π𝒩;𝒩 := by
    apply HasType.pi_intro
    apply HasType.var
    apply IsType.nat_form
    exact hΓctx
  apply HasType.pi_elim this
  exact HasType.nat_zero_intro hΓctx

ttheorem lam_nat_app_zero_nat : ε ⊢ (λ(n : 𝒩). n) ◃ 𝓏 : 𝒩
example : (Γ ctx) -> Γ ⊢ (λ𝒩;v(0)) ◃ 𝓏 ∶ 𝒩 := intro_ctx lam_nat_app_zero_nat
