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

ttheorem fun_ext : ε ⬝ (A : 𝒰) ⬝ (B : 𝒰) ⬝ (f : A → B) ⊢ λ(a : A). (f ◃ a) : A → B

ttheorem subst_b : ε ⊢ ((λ (a : 𝟙). a))◃ ⋆ ≡ ⋆ : 𝟙
ttheorem subst_b' : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) : 𝟙
ttheorem subst_ : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) : 𝟙
ttheorem subst_b'' : ε ⊢ ((λ (A : 𝒰). A) ◃ 𝟙) ≡ 𝟙 : 𝒰
--ttheorem subst_b''' : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙)) ≡ ⋆ : 𝟙
--ttheorem subst_b'''' : ε ⊢ (((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆) ≡ ⋆ : 𝟙

def π₁ : Tm n :=
  λ𝒰; λ(Πv(0);𝒰); λ(Σv(1);(Πv(2);𝒰)); (.indSigma v(2) (Πv(3);𝒰) (v(3)) (v(1)) (v(0)))

def π₁' :=
  [atm|λ (A : 𝒰) . λ (B : Π (a : A ; 𝒰)) . λ (p : Σ (a : A ; B ◃ a)) . indS(p a b A B (λ (z : Σ (x : A ; B ◃ x)) . A) a p)]

def PI₁' := [atm| Π (A : 𝒰 ; Π (B : (Π (x : A ; 𝒰)) ; Π (p : (Σ (x : A ; B ◃ x)) ; A)))]

ttheorem pi1_type : ε ⊢ π₁' : PI₁'

theorem proj_one_type' :
    (ε ⊢ π₁ ∶ Π𝒰; Π(Πv(0);𝒰); Π(Σv(1);(Πv(2);𝒰)); v(2)) :=
  sorry


#eval (v(0)⌈⋆⌉₀ : Tm 0)
--#eval ([atm|λ x⌈⋆⌉₀] : Tm 0)

def π₂ : Tm n :=
  λ𝒰; λ(Πv(0);𝒰); λ(Σv(1);(Πv(2);𝒰)); (.indSigma v(2) (Πv(3);𝒰)
    ((Πv(3);𝒰)⌈π₁◃v(3)◃(Πv(3);𝒰)◃v(0)⌉₀)
    (v(0)) (v(0)))

--def π₂' := [atm|λ (A : 𝒰) . λ (B : Π (a : A ; 𝒰)) . λ (p : Σ (a : A ; B ◃ a)) . indS(p a b A B (λ (z : Σ (x : A ; B ◃ x)) . B ◃ (indS(z x y A B (λ (w : Σ (u : A ; B ◃ u)) . A) x z))) b p)]

instance : ToString (Except String (PLift α)) where
  toString e := match e with
    | .error s => s
    | .ok _ => "success"
#eval is_eq_term fuel ACtx.empty
  (([atm| ⋆])⌊ₐ↑ₚidₚ⌋⌈ₐ[atm|⋆]⌉₀)
  ([atm| ((λ (A : 𝒰). (λ (a : A). a)) ◃ 𝟙) ◃ ⋆])
  ([atm| 𝟙])

#check (ε ⊢ ⋆ ∶ 𝟙)

example (h : Γ ⊢ (t⌈ₐa⌉₀).toTm ∶ T) :
    (Γ ⊢ t.toTm⌈a.toTm⌉₀ ∶ T) := toTm_subst .. ▸ h

theorem fun_ext' : ε ⬝ 𝒰 ⬝ 𝒰 ⬝ (Πv(1);v(1)) ⊢ λv(2);(v(1)◃v(0)) ≡ v(0) ∶ (Πv(2);v(2)) := by
  sorry
