import IMLTT.typed.checked.Elaboration

def my_id := [atm| λ (T : 𝒰). λ (x : T) . x]

ttheorem uid : ε ⬝ (myT : 𝒰) ⬝ (x : myT) ⊢ ((my_id ◃ myT) ◃ x) : myT

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
  exact ((is_type 4 _ _ _).toOption.get (by native_decide)).down

example : ε ⊢ 𝟙 ≡ 𝟙 type := IsEqualType.unit_form_eq IsCtx.empty
example : ε ⊢ 𝟙 ≡ 𝟙 type :=
  IsEqualType.univ_elim_eq <| IsEqualTerm.univ_unit_eq IsCtx.empty

ttheorem type_rfl : ε ⬝ (A : 𝒰) ⊢ A ≡ A type
ttheorem elem_rlf : ε ⬝ (A : 𝒰) ⬝ (a : A) ⊢ a ≡ a : A

ttheorem fun_ext : ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (f : A → B) ⊢ λ(a : A). (f ◃ a) : A → B

ttheorem subst_b : ε ⊢ ((λ (a : 𝟙). a))◃ ⋆ ≡ ⋆ : 𝟙
ttheorem subst_b' : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) : 𝟙
ttheorem subst_ : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) : 𝟙
ttheorem subst_b'' : ε ⊢ ((λ (A : 𝒰). A) ◃ 𝟙) ≡ 𝟙 : 𝒰

example (h : Γ ⊢ (t⌈ₐa⌉₀).toTm ∶ T) :
    (Γ ⊢ t.toTm⌈a.toTm⌉₀ ∶ T) := toTm_subst .. ▸ h

ttheorem pi_type : ε ⬝ (s : 𝟙) ⊢ (λ(x : 𝟙). s) : 𝟙 → 𝟙

ttheorem comp_func : ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⬝ (a : A) ⊢
  (λ(g : B → C). (λ(f : A → B). (λ(x : A).  (g◃(f◃x))))) : (B → C) → (A → B) → (A → C)

ttheorem comp_applied : ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (C : 𝒰) ⬝ (g' : B → C) ⬝ (f' : A → B) ⊢
    ((λ(g : B → C) . (λ(f : A → B) . (λ(x : A) . g ◃ (f ◃ x)))) ◃ g')  ◃ f' : A → C
