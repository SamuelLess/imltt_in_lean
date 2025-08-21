import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.Composition
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution
import IMLTT.untyped.proofs.Conversion

-- comp_weaken

theorem weakening_var_comp {ρ : Weak l m} {ρ' : Weak m n} {x : Fin n} :
    x⌊ρ'⌋ᵥ⌊ρ⌋ᵥ = x⌊ρ ₚ∘ₚρ'⌋ᵥ :=
  by
    induction ρ with
    | id =>
      simp []
    | shift γ ih =>
      simp_all
    | lift γ ih =>
      cases ρ' with
      | id =>
        simp_all
      | shift γ' =>
        simp_all
        rw [←ih]
        rfl
      | lift γ' =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero => rfl
          | succ i' =>
            rw [comp_weaken]
            simp [weaken_var]
            rw [←weakening_var_comp]
            rfl

theorem weakening_comp {ρ : Weak l m} {ρ' : Weak m n} {t : Tm n} :
    t⌊ρ'⌋⌊ρ⌋ = t⌊ρ ₚ∘ₚρ'⌋ :=
  by
    match t with
    | .unit =>
      rfl
    | .empty =>
      rfl
    | .pi A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .sigma A B =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .nat =>
      rfl
    | .iden A a a' =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply And.intro
        · apply weakening_comp
        · apply weakening_comp
    | .univ =>
      rfl
    | .var x =>
      simp [weakening_var_comp]
    | .tt =>
      rfl
    | .indUnit A b a =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply And.intro
        · apply weakening_comp
        · apply weakening_comp
    | .indEmpty A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .lam A b =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .app f a =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .pairSigma a b =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .indSigma A B C c p =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply And.intro
        · apply weakening_comp
        · apply And.intro
          · apply weakening_comp
          · apply And.intro
            · apply weakening_comp
            · apply weakening_comp
    | .zeroNat =>
      simp [weaken]
    | .succNat i =>
      simp [weaken]
      apply weakening_comp
    | .indNat A z s i =>
      simp [weaken]
      repeat' apply And.intro
      · apply weakening_comp
      · apply weakening_comp
      · apply weakening_comp
      · apply weakening_comp
    | .refl A a =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply weakening_comp
    | .j A B b a a' p =>
      simp [weaken]
      apply And.intro
      · apply weakening_comp
      · apply And.intro
        · apply weakening_comp
        · apply And.intro
          · apply weakening_comp
          · apply And.intro
            · apply weakening_comp
            · apply And.intro
              · apply weakening_comp
              · apply weakening_comp

@[simp]
theorem weakening_shift_id {ρ : Weak m n} {t : Tm n} :
    t⌊ρ⌋⌊↑ₚidₚ⌋ = t⌊↑ₚρ⌋ :=
  by
    simp [weakening_comp]

@[simp]
theorem weakening_shift_id_lift {ρ : Weak m n} {t : Tm n} :
    t⌊↑ₚidₚ⌋⌊⇑ₚρ⌋ = t⌊↑ₚρ⌋ :=
  by
    simp [weakening_comp]
    rw [←weakening_shift_id]
    simp [←weakening_comp]

-- comp_weaken_substitute

theorem substitution_lift_comp_ρσ {t : Tm (n + 1)} :
    t⌈⇑ₚρ ₚ∘ₛ⇑ₛσ⌉ = t⌈⇑ₛ(ρ ₚ∘ₛσ)⌉ :=
  by
    simp []

theorem substitution_var_lift_n_comp_ρσ {n : Nat} {x : Fin (z + n + 1)} :
    v(x)⌈⇑ₚ n ₙ⇑ₚρ ₚ∘ₛ⇑ₛ n ₙ⇑ₛσ⌉ = v(x)⌈⇑ₛ n ₙ⇑ₛ(ρ ₚ∘ₛσ)⌉ :=
  by
    match n with
    | .zero =>
      simp []
    | .succ n' =>
      match x with
      | .mk i hFin =>
        match i with
        | .zero =>
          simp []
          rfl
        | .succ i' =>
          rw [comp_weaken_substitute]
          apply substitution_var_lift
          apply substitution_var_lift_n_comp_ρσ

theorem substitution_lift_n_comp_ρσ (l : Nat) {t : Tm (n + l)} :
    t⌈l ₙ⇑ₚρ ₚ∘ₛl ₙ⇑ₛσ⌉ = t⌈l ₙ⇑ₛ(ρ ₚ∘ₛσ)⌉ :=
  by
    match l with
    | 0 =>
      simp []
    | l' + 1 =>
      rw [lift_subst_n]
      rw [lift_weak_n]
      apply substitution_var_substitute
      apply substitution_var_lift_n_comp_ρσ

mutual
  theorem substitution_var_shift_comp_ρσ {x : Fin n} :
      x⌈↑ₛ(ρ ₚ∘ₛσ)⌉ᵥ = x⌈(↑ₚρ ₚ∘ₛσ)⌉ᵥ :=
    by
      induction ρ generalizing x with
      | id =>
        simp []
        cases σ with
        | weak ξ =>
          simp []
        | shift σ' =>
          simp []
        | lift σ' =>
          simp []
        | extend σ' s =>
          rw [comp_weaken_substitute]
          simp only [substitute_var]
          cases x with
          | mk i hFin =>
            cases i with
            | zero => rfl
            | succ i' => apply substitution_var_comp_ρσ
      | shift ρ' ih =>
        cases σ with
        | weak ξ =>
          simp []
        | shift σ' =>
          simp []
        | lift σ' =>
          simp []
        | extend σ' s =>
          simp only [substitute_var, shift_tm, comp_weaken_substitute]
          cases x with
          | mk i hFin =>
            cases i with
            | zero =>
              simp [weakening_comp]
            | succ i' =>
              simp []
              rw (config := {occs := .pos [2]}) [←substitution_var_shift_comp_ρσ]
              rfl
      | lift ρ' ih =>
        cases σ with
        | weak ξ =>
          simp []
        | shift σ' =>
          simp []
        | lift σ' =>
          simp []
        | extend σ' s =>
          simp only [substitute_var, shift_tm, comp_weaken_substitute]
          cases x with
          | mk i hFin =>
            cases i with
            | zero =>
              simp [weakening_comp]
            | succ i' =>
              simp []
              rw [←substitution_var_shift_comp_ρσ]
              simp only [substitute_var, shift_tm]

  theorem substitution_var_comp_ρσ {ρ : Weak l m} {σ : Subst m n} {x : Fin n} :
      x⌈σ⌉ᵥ⌊ρ⌋ = x⌈ρ ₚ∘ₛσ⌉ᵥ :=
    by
      induction ρ with
      | id =>
        simp []
      | shift ρ' ih =>
        cases σ with
        | weak γ =>
          simp [weakening_var_comp]
        | shift σ' =>
          rw [←weakening_shift_id]
          simp [←ih]
        | lift σ' =>
          rw [comp_weaken_substitute]
          rw (config := {occs := .pos [1]}) [substitute_var]
          rw [←ih, shift_tm, weakening_comp, comp_weaken, comp_weaken]
        | extend σ' s =>
          rw [←weakening_shift_id, ih]
          simp only [comp_weaken_substitute, substitute_var]
          rw [substitution_var_conv_shift_id]
          simp only [substitute_var]
          cases x with
          | mk i hFin =>
            cases i with
            | zero =>
              simp only [←ih, shift_tm, substitute_var, weakening_shift_id]
            | succ i' =>
              simp [←substitution_var_shift_comp_ρσ, ←ih, ←substitution_var_comp_ρσ]
      | lift ρ' ih =>
        cases σ with
        | weak γ =>
          simp only [comp_weaken_substitute]
          simp only [substitution_weakening_var]
          rw [weaken]
          simp only [weakening_var_comp]
        | shift σ' =>
          simp only [comp_weaken_substitute]
          simp only [substitute_var]
          simp only [shift_tm]
          simp only [weakening_shift_id_lift]
          rw [←weakening_shift_id]
          exact congrArg (weaken (↑ₚidₚ)) ih
        | lift σ' =>
          cases x with
          | mk i hFin =>
            cases i with
            | zero =>
              simp [comp_weaken_substitute]
              rfl
            | succ i' =>
              simp only [comp_weaken_substitute, substitute_var,
                  shift_tm, weakening_comp, comp_weaken]
              rw [←weakening_shift_id]
              simp only [←weakening_comp, weakening_id, ←substitution_conv_var]
              rw [substitute, substitution_var_comp_ρσ]
              rfl
        | extend σ' s =>
          cases x with
          | mk i hFin =>
            cases i with
            | zero =>
              simp only [comp_weaken_substitute, substitute_var]
            | succ i' =>
              simp only [comp_weaken_substitute, substitute_var, ←substitution_conv_var]
              simp_all only [substitute, substitute_var]
              simp only [substitution_var_comp_ρσ]
end

theorem substitution_comp_ρσ {t : Tm n} :
    t⌈σ⌉⌊ρ⌋ = t⌈ρ ₚ∘ₛσ⌉ :=
  by
    match t with
    | .unit =>
      rfl
    | .empty =>
      rfl
    | .pi A B =>
      simp []
      apply And.intro
      · apply substitution_comp_ρσ
      · rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
    | .sigma A B =>
      simp []
      apply And.intro
      · apply substitution_comp_ρσ
      · rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
    | .nat =>
      rfl
    | .iden A a a' =>
      simp []
      apply And.intro
      · apply substitution_comp_ρσ
      · apply And.intro
        · apply substitution_comp_ρσ
        · apply substitution_comp_ρσ
    | .univ =>
      rfl
    | .var x =>
      simp [substitution_var_comp_ρσ]
    | .tt =>
      rfl
    | .indUnit A b a =>
      simp []
      apply And.intro
      · rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
      · apply And.intro
        · apply substitution_comp_ρσ
        · apply substitution_comp_ρσ
    | .indEmpty A b =>
      simp []
      apply And.intro
      · rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .lam A b =>
      simp []
      apply And.intro
      · apply substitution_comp_ρσ
      · rw [←substitution_lift_comp_ρσ]
        apply substitution_comp_ρσ
    | .app f a =>
      simp []
      apply And.intro
      · apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .pairSigma a b =>
      simp []
      apply And.intro
      · apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .indSigma A B C c p =>
      simp [-lift_weak_n, -lift_subst_n]
      apply And.intro
      · apply substitution_comp_ρσ
      · apply And.intro
        · rw [←substitution_lift_n_comp_ρσ]
          apply substitution_comp_ρσ
        · apply And.intro
          · rw [←substitution_lift_n_comp_ρσ]
            apply substitution_comp_ρσ
          · apply And.intro
            · rw [←substitution_lift_n_comp_ρσ]
              apply substitution_comp_ρσ
            · apply substitution_comp_ρσ
    | .zeroNat =>
      simp []
    | .succNat i =>
      simp []
      apply substitution_comp_ρσ
    | .indNat A z s i =>
      simp [-lift_weak_n, -lift_subst_n]
      repeat' apply And.intro
      · rw [←substitution_lift_n_comp_ρσ]
        apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
      · rw [←substitution_lift_n_comp_ρσ]
        apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .refl A a =>
      simp []
      apply And.intro
      · apply substitution_comp_ρσ
      · apply substitution_comp_ρσ
    | .j A B b a a' p =>
      simp [-lift_weak_n, -lift_subst_n]
      apply And.intro
      · apply substitution_comp_ρσ
      · apply And.intro
        · rw [←substitution_lift_n_comp_ρσ]
          apply substitution_comp_ρσ
        · apply And.intro
          · rw [←substitution_lift_n_comp_ρσ]
            apply substitution_comp_ρσ
          · apply And.intro
            · apply substitution_comp_ρσ
            · apply And.intro
              · apply substitution_comp_ρσ
              · apply substitution_comp_ρσ

@[simp]
theorem substitution_conv_shift_id :
    t⌈σ⌉⌊↑ₚidₚ⌋ = t⌈↑ₛσ⌉ :=
  by
    simp [substitution_comp_ρσ]
    apply substitution_var_substitute
    simp [←substitution_var_comp_ρσ]

-- comp_substitute_weaken

theorem substitution_lift_comp_σρ {t : Tm (n + 1)} :
    t⌈⇑ₛσ ₛ∘ₚ⇑ₚρ⌉ = t⌈⇑ₛ(σ ₛ∘ₚρ)⌉ :=
  by
    rfl

theorem substitution_var_lift_n_comp_σρ {l : Nat} {x : Fin (n + l + 1)} :
    v(x)⌈⇑ₛ l ₙ⇑ₛσ ₛ∘ₚ ⇑ₚ l ₙ⇑ₚρ⌉ = v(x)⌈⇑ₛ l ₙ⇑ₛ(σ ₛ∘ₚρ)⌉ :=
  by
    match l with
    | .zero =>
      match x with
      | .mk i hFin =>
        match i with
        | .zero =>
          rfl
        | .succ i' =>
          simp []
    | .succ n' =>
      match x with
      | .mk i hFin =>
        match i with
        | .zero =>
          rfl
        | .succ i' =>
          rw [comp_substitute_weaken]
          apply substitution_var_lift
          apply substitution_var_lift_n_comp_σρ

theorem substitution_lift_n_comp_σρ {l : Nat} {t : Tm (n + l)} :
    t⌈l ₙ⇑ₛσ ₛ∘ₚl ₙ⇑ₚρ⌉ = t⌈l ₙ⇑ₛ(σ ₛ∘ₚρ)⌉ :=
  by
    match l with
    | .zero => rfl
    | .succ l' =>
      apply substitution_var_substitute
      apply substitution_var_lift_n_comp_σρ

@[simp]
theorem substitution_var_shift_id_lift :
    v(x)⌊↑ₚidₚ⌋⌈⇑ₛσ⌉ = v(x)⌈↑ₛσ⌉ :=
  by
    simp []
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        simp []
      | succ i' =>
        simp []

theorem substitution_var_comp_σρ {x : Fin n} :
    x⌊ρ⌋ᵥ⌈σ⌉ᵥ = x⌈σ ₛ∘ₚρ⌉ᵥ :=
  by
    induction σ with
    | weak ξ =>
      cases ρ with
      | id =>
        simp []
      | shift ρ' =>
        simp only [comp_substitute_weaken]
        simp only [substitution_weakening_var]
        simp [←weakening_var_comp]
      | lift ρ' =>
        simp only [comp_substitute_weaken]
        simp only [substitution_weakening_var]
        simp [←weakening_var_comp]
    | shift σ' ih =>
      cases ρ with
      | id =>
        simp [comp_substitute_weaken]
      | shift ρ' =>
        simp only [comp_substitute_weaken]
        simp only [←substitution_var_conv_shift_id]
        simp only [←substitution_conv_var]
        simp [←ih]
      | lift ρ' =>
        simp only [comp_substitute_weaken]
        simp only [←substitution_var_conv_shift_id]
        simp only [←substitution_conv_var]
        simp [←ih]
    | lift σ' ih =>
      cases ρ with
      | id =>
        simp [comp_substitute_weaken]
      | shift ρ' =>
        simp only [comp_substitute_weaken]
        simp only [substitute_var]
        rw [←ih]
        simp []
        rfl
      | lift ρ' =>
        simp only [comp_substitute_weaken]
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp []
            rfl
          | succ i' =>
            simp only [substitute_var]
            simp only [shift_tm]
            rw [←substitution_var_comp_σρ]
            rfl
    | extend σ' s ih =>
      cases ρ with
      | id =>
        simp []
      | shift ρ' =>
        simp [comp_substitute_weaken]
        simp [←ih]
        rfl
      | lift ρ' =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp [comp_substitute_weaken]
            rfl
          | succ i' =>
            simp [comp_substitute_weaken]
            simp [←substitution_var_comp_σρ]
            rfl

theorem substitution_comp_σρ {t : Tm n} :
    t⌊ρ⌋⌈σ⌉ = t⌈σ ₛ∘ₚρ⌉ :=
  by
    match t with
    | .unit =>
      rfl
    | .empty =>
      rfl
    | .pi A B =>
      simp []
      apply And.intro
      · apply substitution_comp_σρ
      · rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
    | .sigma A B =>
      simp []
      apply And.intro
      · apply substitution_comp_σρ
      · rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
    | .nat =>
      rfl
    | .iden A a a' =>
      simp []
      apply And.intro
      · apply substitution_comp_σρ
      · apply And.intro
        · apply substitution_comp_σρ
        · apply substitution_comp_σρ
    | .univ =>
      rfl
    | .var x =>
      apply substitution_var_comp_σρ
    | .tt =>
      rfl
    | .indUnit A b a =>
      simp []
      apply And.intro
      · rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
      · apply And.intro
        · apply substitution_comp_σρ
        · apply substitution_comp_σρ
    | .indEmpty A b =>
      simp []
      apply And.intro
      · rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .lam A b =>
      simp []
      apply And.intro
      · apply substitution_comp_σρ
      · rw [←substitution_lift_comp_σρ]
        apply substitution_comp_σρ
    | .app f a =>
      simp []
      apply And.intro
      · apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .pairSigma a b =>
      simp []
      apply And.intro
      · apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .indSigma A B C c p =>
      simp [-lift_subst_n, -lift_weak_n]
      apply And.intro
      · apply substitution_comp_σρ
      · apply And.intro
        · rw [←substitution_lift_n_comp_σρ]
          apply substitution_comp_σρ
        · apply And.intro
          · rw [←substitution_lift_n_comp_σρ]
            apply substitution_comp_σρ
          · apply And.intro
            · rw [←substitution_lift_n_comp_σρ]
              apply substitution_comp_σρ
            · apply substitution_comp_σρ
    | .zeroNat =>
      simp []
    | .succNat i =>
      simp []
      apply substitution_comp_σρ
    | .indNat A z s i =>
      simp [-lift_weak_n, -lift_subst_n]
      repeat' apply And.intro
      · rw [←substitution_lift_n_comp_σρ]
        apply substitution_comp_σρ
      · apply substitution_comp_σρ
      · rw [←substitution_lift_n_comp_σρ]
        apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .refl A a =>
      simp []
      apply And.intro
      · apply substitution_comp_σρ
      · apply substitution_comp_σρ
    | .j A B b a a' p =>
      simp [-lift_weak_n, -lift_subst_n]
      apply And.intro
      · apply substitution_comp_σρ
      · apply And.intro
        · rw [←substitution_lift_n_comp_σρ]
          apply substitution_comp_σρ
        · apply And.intro
          · apply substitution_comp_σρ
          · apply And.intro
            · apply substitution_comp_σρ
            · apply And.intro
              · apply substitution_comp_σρ
              · apply substitution_comp_σρ

@[simp]
theorem substitution_shift_id_lift :
    t⌊↑ₚidₚ⌋⌈⇑ₛσ⌉ = t⌈σ⌉⌊↑ₚidₚ⌋ :=
  by
    simp [substitution_conv_shift_id]
    simp [substitution_comp_σρ]

-- comp_substitute_substitute

theorem substitution_lift_comp :
    t⌈⇑ₛσ ₛ∘ₛ⇑ₛσ'⌉ = t⌈⇑ₛ(σ ₛ∘ₛσ')⌉ :=
  by
    simp [comp_substitute_substitute]

theorem substitution_var_lift_n_comp :
    v(x)⌈⇑ₛ n ₙ⇑ₛσ ₛ∘ₛ ⇑ₛ n ₙ⇑ₛσ'⌉ = v(x)⌈⇑ₛn ₙ⇑ₛ(σ ₛ∘ₛσ')⌉ :=
  by
    cases n with
    | zero =>
      simp [lift_subst_n]
    | succ n' =>
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          simp [comp_substitute_substitute]
          rfl
        | succ i' =>
          simp only [comp_substitute_substitute]
          apply substitution_var_lift
          simp only [lift_subst_n]
          apply substitution_var_lift_n_comp

theorem substitution_lift_n_comp (l : Nat) {t : Tm (n + l)} :
    t⌈l ₙ⇑ₛσ ₛ∘ₛl ₙ⇑ₛσ'⌉ = t⌈l ₙ⇑ₛ(σ ₛ∘ₛ σ')⌉ :=
  by
    match l with
    | 0 =>
      simp [lift_subst_n]
    | l' + 1 =>
      simp only [lift_subst_n]
      apply substitution_var_substitute
      apply substitution_var_lift_n_comp

theorem substitution_var_comp {x : Fin n} :
    x⌈σ'⌉ᵥ⌈σ⌉ = x⌈σ ₛ∘ₛσ'⌉ᵥ :=
  by
    induction σ' with
    | weak ρ' =>
      simp [substitution_var_comp_σρ]
    | shift ξ' ih =>
      cases σ with
      | weak ρ =>
        simp only [comp_substitute_substitute]
        simp only [←substitution_var_comp_ρσ]
        simp only [conversion_sub_weak]
      | shift ξ =>
        simp only [comp_substitute_substitute]
        simp only [←substitution_conv_var]
        simp only [←substitution_conv_shift_id]
        simp [←substitution_var_comp]
      | lift ξ =>
        simp only [comp_substitute_substitute]
        simp only [←substitution_var_conv_shift_id]
        simp only [←substitution_conv_var]
        simp [←substitution_var_comp]
      | extend ξ s =>
        simp [comp_substitute_substitute]
        rw [←ih]
        simp [substitution_comp_σρ]
    | lift ξ' ih =>
      cases σ with
      | weak ρ =>
        simp only [comp_substitute_substitute]
        simp [←substitution_var_comp_ρσ]
      | shift ξ =>
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp only [substitute_var]
            simp only [comp_substitute_substitute]
            simp only [←substitution_var_conv_shift_id]
            simp only [←substitution_conv_var]
            simp [←substitution_var_comp]
            aesop
          | succ i' =>
            simp only [substitute_var]
            simp only [shift_tm]
            simp only [comp_substitute_substitute]
            simp only [←substitution_var_conv_shift_id]
            simp only [←substitution_conv_var]
            simp [←substitution_var_comp]
      | lift ξ =>
        simp only [comp_substitute_substitute]
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp []
            rfl
          | succ i' =>
            simp only [substitute_var]
            simp only [shift_tm]
            simp only [←substitution_conv_var]
            simp [←substitution_var_comp]
      | extend ξ s =>
        simp only [comp_substitute_substitute]
        cases x with
        | mk i hFin =>
          cases i with
          | zero =>
            simp []
            rfl
          | succ i' =>
            simp only [substitute_var]
            simp only [shift_tm]
            simp only [substitution_comp_σρ]
            simp only [comp_substitute_weaken]
            simp only [←substitution_conv_var]
            simp [ih]
    | extend ξ' s' ih =>
      simp [comp_substitute_substitute]
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          simp []
        | succ i' =>
          simp []
          rw [←substitution_conv_var]
          rw [←ih]
          rfl

theorem substitution_comp :
    t⌈σ'⌉⌈σ⌉ = t⌈σ ₛ∘ₛ σ'⌉ :=
  by
    cases t with
    | unit =>
      simp [substitute]
    | empty =>
      simp [substitute]
    | pi A B =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · rw [←substitution_lift_comp]
        apply substitution_comp
    | sigma A B =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · rw [←substitution_lift_comp]
        apply substitution_comp
    | nat =>
      simp [substitute]
    | iden A a a' =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply And.intro
        · apply substitution_comp
        · apply substitution_comp
    | univ =>
      simp [substitute]
    | var x =>
      apply substitution_var_comp
    | tt =>
      simp [substitute]
    | indUnit A b a =>
      simp [substitute]
      apply And.intro
      · rw [←substitution_lift_comp]
        apply substitution_comp
      · apply And.intro
        · apply substitution_comp
        · apply substitution_comp
    | indEmpty A b =>
      simp [substitute]
      apply And.intro
      · rw [←substitution_lift_comp]
        apply substitution_comp
      · apply substitution_comp
    | lam A b =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · rw [←substitution_lift_comp]
        apply substitution_comp
    | app f a =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply substitution_comp
    | pairSigma a b =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply substitution_comp
    | indSigma A B C c p =>
      simp [-lift_subst_n]
      apply And.intro
      · apply substitution_comp
      · apply And.intro
        · rw [←substitution_lift_n_comp]
          apply substitution_comp
        · apply And.intro
          · rw [←substitution_lift_n_comp]
            apply substitution_comp
          · apply And.intro
            · rw [←substitution_lift_n_comp]
              apply substitution_comp
            · apply substitution_comp
    | zeroNat =>
      simp [substitute]
    | succNat i =>
      simp [substitute]
      apply substitution_comp
    | indNat A z s i =>
      simp [-lift_subst_n]
      repeat' apply And.intro
      · rw [←substitution_lift_n_comp]
        apply substitution_comp
      · apply substitution_comp
      · rw [←substitution_lift_n_comp]
        apply substitution_comp
      · apply substitution_comp
    | refl A a =>
      simp [substitute]
      apply And.intro
      · apply substitution_comp
      · apply substitution_comp
    | j A B b a a' p =>
      simp [-lift_subst_n]
      apply And.intro
      · apply substitution_comp
      · apply And.intro
        · rw [←substitution_lift_n_comp]
          apply substitution_comp
        · apply And.intro
          · rw [←substitution_lift_n_comp]
            apply substitution_comp
          · apply And.intro
            · apply substitution_comp
            · apply And.intro
              · apply substitution_comp
              · apply substitution_comp
