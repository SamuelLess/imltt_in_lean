import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution
import IMLTT.untyped.proofs.Weakening
import IMLTT.untyped.proofs.Substitution

theorem substitution_conv_var :
    v(x)⌈σ⌉ = x⌈σ⌉ᵥ :=
  by
    simp [substitute]

theorem substitution_conv_zero :
    t⌈(ₛidₚ)⋄ σ⌉ = t⌈σ⌉₀ :=
  by
    simp [substitute_zero]

theorem zero_substitution_conv :
    t⌈(ₛidₚ)⋄ σ⌉ = t⌈σ/₀⌉ :=
  by
    simp [zero_substitution]

theorem conversion_var_lift :
    (∀ (x : Fin n), v(x)⌈σ⌉ = v(x)⌊ρ⌋) → ∀ (x : Fin (n + 1)), v(x)⌈⇑ₛσ⌉ = v(x)⌊⇑ₚρ⌋ :=
  by
    intro h x
    cases x with
    | mk i hFin =>
      cases i with
      | zero =>
        rfl
      | succ i' =>
        apply congrArg shift_tm (h (.mk i' (Nat.lt_of_succ_lt_succ hFin)))

theorem conversion_var_lift_n :
    (∀x, v(x)⌈σ⌉ = v(x)⌊ρ⌋) → ∀x, v(x)⌈l ₙ⇑ₛσ⌉ = v(x)⌊l ₙ⇑ₚρ⌋ :=
  by
    intro h x
    cases l with
    | zero =>
      aesop
    | succ i' =>
      cases x with
      | mk i hFin =>
        cases i with
        | zero =>
          rfl
        | succ i' =>
          rw [lift_subst_n]
          rw [lift_weak_n]
          apply conversion_var_lift
          apply conversion_var_lift_n
          apply h

@[aesop safe apply]
theorem conversion_var_substitute {σ σ' : Subst m n} :
    (∀x, v(x)⌈σ⌉ = v(x)⌊ρ⌋) → ∀t, t⌈σ⌉ = t⌊ρ⌋ :=
  by
    intro h t
    match t with
    | .unit =>
      simp [substitute]
    | .empty =>
      simp [substitute]
    | .pi A B =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
    | .sigma A B =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
    | .nat =>
      simp [substitute]
    | .iden A a a' =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply And.intro
        · apply conversion_var_substitute h
          assumption
        · apply conversion_var_substitute h
          assumption
    | .univ =>
      simp [substitute]
    | .var x =>
      apply h
    | .tt =>
      simp [substitute]
    | .indUnit A b a =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
      · apply And.intro
        · apply conversion_var_substitute h
          assumption
        · apply conversion_var_substitute h
          assumption
    | .indEmpty A b =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
      · apply conversion_var_substitute h
        assumption
    | .lam A b => 
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
    | .app f a => 
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute h
        assumption
    | .pairSigma a b =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute h
        assumption
    | .indSigma A B C c p =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply And.intro
        · apply conversion_var_substitute
          · have ξ := lift_subst_n 1 σ
            apply ξ
          · apply conversion_var_lift_n h
        · apply And.intro
          · apply conversion_var_substitute
            · have ξ := lift_subst_n 1 σ
              apply ξ
            · apply conversion_var_lift_n h
          · apply And.intro
            · apply conversion_var_substitute
              · have ξ := lift_subst_n 2 σ
                apply ξ
              · apply conversion_var_lift_n h
            · apply conversion_var_substitute h
              assumption
    | .zeroNat =>
      simp [substitute]
    | .succNat i =>
      simp [substitute]
      apply conversion_var_substitute h
      assumption
    | .indNat A z s i =>
      simp [substitute]
      repeat' apply And.intro
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 1 σ
          apply ξ
        · apply conversion_var_lift_n h
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute
        · have ξ := lift_subst_n 2 σ
          apply ξ
        · apply conversion_var_lift_n h
      · apply conversion_var_substitute h
        assumption
    | .refl A a =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply conversion_var_substitute h
        assumption
    | .j A B b a a' p => 
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute h
        assumption
      · apply And.intro
        · apply conversion_var_substitute
          · have ξ := lift_subst_n 3 σ
            apply ξ
          · apply conversion_var_lift_n h
        · apply And.intro
          · apply conversion_var_substitute
            · have ξ := lift_subst_n 1 σ
              apply ξ
            · apply conversion_var_lift_n h
          · apply And.intro
            · apply conversion_var_substitute h
              assumption
            · apply And.intro
              · apply conversion_var_substitute h
                assumption
              · apply conversion_var_substitute h
                assumption

@[simp]
theorem conversion_var_sub_weak :
    v(x)⌈ₛρ⌉ = v(x)⌊ρ⌋ :=
  by
    simp [substitute]

@[simp]
theorem conversion_sub_weak :
    t⌈ₛρ⌉ = t⌊ρ⌋ :=
  by
    cases t with
    | unit =>
      simp [substitute]
    | empty =>
      simp [substitute]
    | pi A B =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
    | sigma A B =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
    | nat =>
      simp [substitute]
    | iden A a a' =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply And.intro
        · apply conversion_sub_weak
        · apply conversion_sub_weak
    | univ =>
      simp [substitute]
    | var x =>
      apply conversion_var_sub_weak
    | tt =>
      simp [substitute]
    | indUnit A b a =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
      · apply And.intro
        · apply conversion_sub_weak
        · apply conversion_sub_weak
    | indEmpty A b =>
      simp [substitute]
      apply And.intro
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
      · apply conversion_sub_weak
    | lam A b =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
    | app f a =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_sub_weak
    | pairSigma a b =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_sub_weak
    | indSigma A B C c p =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply And.intro
        · apply conversion_var_substitute
          · apply lift_subst_n 1 (.weak ρ)
          · apply conversion_var_lift_n
            apply conversion_var_sub_weak
        · apply And.intro
          · apply conversion_var_substitute
            · apply lift_subst_n 1 (.weak ρ)
            · apply conversion_var_lift_n
              apply conversion_var_sub_weak
          · apply And.intro
            · apply conversion_var_substitute
              · apply lift_subst_n 2 (.weak ρ)
              · apply conversion_var_lift_n
                apply conversion_var_sub_weak
            · apply conversion_sub_weak
    | zeroNat =>
      simp [substitute]
    | succNat i =>
      simp [substitute]
      apply conversion_sub_weak
    | indNat A z s i =>
      simp [substitute]
      repeat' apply And.intro
      · apply conversion_var_substitute
        · apply lift_subst_n 1 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
      · apply conversion_sub_weak
      · apply conversion_var_substitute
        · apply lift_subst_n 2 (.weak ρ)
        · apply conversion_var_lift_n
          apply conversion_var_sub_weak
      · apply conversion_sub_weak
    | refl A a =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply conversion_sub_weak
    | j A B b a a' p =>
      simp [substitute]
      apply And.intro
      · apply conversion_sub_weak
      · apply And.intro
        · apply conversion_var_substitute
          · apply lift_subst_n 3 (.weak ρ)
          · apply conversion_var_lift_n
            apply conversion_var_sub_weak
        · apply And.intro
          · apply conversion_var_substitute
            · apply lift_subst_n 1 (.weak ρ)
            · apply conversion_var_lift_n
              apply conversion_var_sub_weak
          · apply And.intro
            · apply conversion_sub_weak
            · apply And.intro
              · apply conversion_sub_weak
              · apply conversion_sub_weak

theorem substitution_conv_shift :
    x⌈ₛ↑ₚρ⌉ᵥ = x⌈↑ₛ(ₛρ)⌉ᵥ :=
  by
    simp [substitute_var]

theorem substitution_conv_shift_term :
    t⌈ₛ↑ₚρ⌉ = t⌈↑ₛ(ₛρ)⌉ :=
  by
    apply substitution_var_substitute
    intro x
    simp [substitute]

@[simp]
theorem substitution_conv_shift_id_conv :
    t⌈ₛ↑ₚidₚ⌉ = t⌊↑ₚidₚ⌋ :=
  by
    apply conversion_var_substitute
    · apply ₛ↑ₚidₚ
    · intro x
      simp [substitute]

theorem substitution_conv_shift_comp_ρσ :
    ↑ₚρ ₚ∘ₛ (σ⋄ t) = ↑ₛ(ρ ₚ∘ₛ σ⋄ (t⌊ρ⌋)) :=
  by
    simp [comp_weaken_substitute]

theorem substitution_var_conv_shift_id {σ : Subst m n} {x : Fin n} :
    x⌈σ⌉ᵥ⌊↑ₚidₚ⌋ = x⌈↑ₛσ⌉ᵥ :=
  by
    simp [substitute_var]

theorem substitution_conv_comp_ρρ :
    x⌊ρ ₚ∘ₚ ρ'⌋ᵥ = x⌈ρ ₚ∘ₛ (ₛρ')⌉ᵥ :=
  by
    cases ρ with
    | id =>
      simp [comp_weaken_substitute]
    | shift ξ =>
      simp [comp_weaken_substitute]
    | lift ξ =>
      simp [comp_weaken_substitute]


theorem conversion_var_lift_n_sub_weak :
    x⌈lift_subst_n n (ₛρ)⌉ᵥ = x⌊lift_weak_n n ρ⌋ᵥ :=
  by
    induction n with
    | zero =>
      simp []
    | succ n' ih =>
      simp []
      cases x
      case mk i hFin =>
        cases i with
        | zero =>
          simp []
        | succ i' =>
          simp [ih]
