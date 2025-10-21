import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Elaboration
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

theorem bridge : IsCtx Ctx.empty := emptyctx

ttheorem id_is_type : ε ⊢ type_id type

ttheorem typeid1 : ε ⊢ ret_id : type_id
ttheorem typeid2 : ε ⊢ type_id ≡ Π(T : 𝒰;Π (x : T;T)) type
ttheorem typeid3 : ε ⊢ ret_id ≡ ret_id : type_id

ttheorem type_rfl : ε ⬝ (A : 𝒰) ⊢ A ≡ A type
ttheorem elem_rlf : ε ⬝ (A : 𝒰) ⬝ (a : A) ⊢ a ≡ a : A

ttheorem subst_b : ε ⊢ ((λ (a : 𝟙). a))◃ ⋆ ≡ ⋆ : 𝟙
ttheorem subst_b' : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) : 𝟙
ttheorem subst_ : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) : 𝟙
ttheorem subst_b'' : ε ⊢ ((λ (A : 𝒰). A) ◃ 𝟙) ≡ 𝟙 : 𝒰
ttheorem subst_b''' : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙)) ≡ ⋆ : 𝟙
ttheorem subst_b'''' : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) ≡ ⋆ : 𝟙

instance : ToString (Except String (PLift α)) where
  toString e := match e with
    | .error s => s
    | .ok _ => "success"
#eval is_eq_term fuel ACtx.empty
  (([atm| ⋆])⌊ₐ↑ₚidₚ⌋⌈ₐ[atm|⋆]⌉₀)
  ([atm| ((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆])
  ([atm| 𝟙])
