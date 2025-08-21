import IMLTT.untyped.AbstractSyntax
import IMLTT.untyped.Weakening
import IMLTT.untyped.Substitution

import IMLTT.typed.JudgmentsAndRules
import IMLTT.typed.RulesEquality

theorem test_predicativity_one :
    (ε ⊢ Π(Π𝟙;𝒰);𝟙 type) :=
  by
    repeat constructor

theorem test_predicativity_two :
    (ε ⊢ Π(Π𝒰;(Π𝒰;𝟙));𝒰 type) :=
  by
    repeat constructor

theorem test_predicativity_three_test_ :
    (ε ⊢ Π𝒰;𝒰 type) :=
  by
    repeat constructor

theorem test_predicativity_three_test :
    (ε ⊢ Π𝒰;𝒰 ∶ 𝒰) :=
  by
    constructor
    · sorry
    · sorry

theorem test_predicativity_three :
    (ε ⊢ Π(Π𝟙;𝒰);𝟙 ∶ 𝒰) :=
  by
    constructor
    · constructor
      · constructor
        constructor
      · sorry
    · repeat constructor

theorem test_predicativity_four :
    (ε ⊢ Π(Π𝟙;𝒰);𝒰 ∶ 𝒰) :=
  by
    constructor
    · constructor
      · constructor
        constructor
      · sorry
    · sorry

theorem test_predicativity_five :
    (ε ⊢ (Π𝒰;𝟙) ∶ 𝒰) :=
  by
    constructor
    · sorry
    · repeat constructor
