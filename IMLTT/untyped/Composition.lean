import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

@[simp]
def comp_weaken (ρ : Weak l m) (ρ' : Weak m n) : Weak l n :=
  match ρ with
  | .id => ρ'
  | .shift γ => .shift (comp_weaken γ ρ')
    -- X, Y, Z ⊢ Σv(2);v(1) type → (X, Y, Z) ⬝ B ⊢ ↑Σv(2);v(1) type
  | .lift γ  =>
    match ρ' with
    | .id => .lift γ
    | .shift γ' => .shift (comp_weaken γ γ')
    | .lift γ' => .lift (comp_weaken γ γ')

@[simp]
def comp_substitute_weaken (σ : Subst l m) (ρ : Weak m n) : Subst l n :=
  match ρ with
  | .id => σ
  | .shift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken ξ (.shift ρ'))
    | .shift σ' => .shift (comp_substitute_weaken σ' (.shift ρ'))
    | .lift σ' => .shift (comp_substitute_weaken σ' ρ')
    | .extend σ' t => comp_substitute_weaken σ' ρ'
  | .lift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken ξ (.lift ρ'))
    | .shift σ' => .shift (comp_substitute_weaken σ' (.lift ρ'))
    | .lift σ' => .lift (comp_substitute_weaken σ' ρ')
    | .extend σ' t => .extend (comp_substitute_weaken σ' ρ') t

@[simp]
def comp_weaken_substitute (ρ : Weak l m) (σ : Subst m n) : Subst l n :=
  match ρ with
  | .id => σ
  | .shift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken (.shift ρ') ξ)
    | .shift σ' => .shift (comp_weaken_substitute ρ' (.shift σ'))
    | .lift σ' => .shift (comp_weaken_substitute ρ' (.lift σ'))
    | .extend σ' t => (.extend (comp_weaken_substitute (.shift ρ') σ') (weaken (.shift ρ') t))
  | .lift ρ' =>
    match σ with
    | .weak ξ => .weak (comp_weaken (.lift ρ') ξ)
    | .shift σ' => .shift (comp_weaken_substitute ρ' σ')
    | .lift σ' => .lift (comp_weaken_substitute ρ' σ')
    | .extend σ' t => .extend (comp_weaken_substitute (.lift ρ') σ') (weaken (.lift ρ') t)

@[simp]
def comp_substitute_substitute (σ : Subst l m) (σ' : Subst m n) : Subst l n :=
  match σ' with
  | .weak ρ' => comp_substitute_weaken σ ρ'
  | .shift ξ' =>
    match σ with
    | .weak ρ => comp_weaken_substitute ρ (.shift ξ')
    | .shift ξ => .shift (comp_substitute_substitute ξ (.shift ξ'))
    | .lift ξ => .shift (comp_substitute_substitute ξ ξ')
    | .extend ξ t => comp_substitute_substitute ξ ξ'
  | .lift ξ' =>
    match σ with
    | .weak ρ => comp_weaken_substitute ρ (.lift ξ')
    | .shift ξ => .shift (comp_substitute_substitute ξ (.lift ξ'))
    | .lift ξ => .lift (comp_substitute_substitute ξ ξ')
    | .extend ξ t => .extend (comp_substitute_substitute ξ ξ') t
  | .extend ξ' t => .extend (comp_substitute_substitute σ ξ') (substitute σ t)

infixl:96 "ₚ∘ₚ" => comp_weaken
infixl:96 "ₚ∘ₛ" => comp_weaken_substitute
infixl:96 "ₛ∘ₚ" => comp_substitute_weaken
infixl:96 "ₛ∘ₛ" => comp_substitute_substitute
