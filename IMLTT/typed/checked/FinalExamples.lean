import IMLTT.typed.annotated.Syntax
import IMLTT.typed.annotated.Elaboration
import IMLTT.typed.checked.Elaboration

def my_id := [atm| λ (T : 𝒰). λ (x : T) . x]

ttheorem uid : ε ⬝ (myT : 𝒰) ⬝ (x : myT) ⊢ (my_id ◃ myT ◃ x) : myT

def myunit := [atm| 𝟙]

ttheorem wisunit : ε ⬝ (x : 𝟙) ⬝ (y : 𝒰) ⬝ (w : myunit) ⊢ w : 𝟙

ttheorem myid : ε ⬝ (A : 𝒰) ⬝ (IdA : Π(a : A; A)) ⬝ (a : A) ⊢ IdA ◃ a : A

def starp := [atm| (⋆ & ⋆)::Σ(s:𝟙;𝟙)]

ttheorem starpair : ε ⊢ (⋆ & ⋆)::𝟙 : Σ(x : 𝟙; 𝟙)


def ret_id := [atm| (λ(T : 𝒰). λ (x : T). x)]

def natpair : ATm 0 := [atm|((λ (n:𝒩).
    (𝓈(n) & ret_id ◃ 𝒩 ◃ 𝓏) :: Σ(n:𝒩;𝒩)) ◃ 𝓏)]

ttheorem usingnextterm : ε  ⊢ natpair : Σ(x : 𝒩;𝒩)
