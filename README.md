# imltt_in_lean

This fork builds upon the implementation of syntactic properties of an intensional Martin-Löf type theory and embeds it as a domain-specific language in Lean for writing terms and judgments. 
This custom 'frontend' includes named variables instead of de Bruijn indices, localized error messages, and the ability to use global constants across terms.
Furthermore, parts of a proof-generating typechecker are implemented and used to automatically create Lean theorems for expressed judgments.

# Overview of contributions of this fork
The following folders and files have been added.
```
├── IMLTT
│   ├── typed
│   │   ├── annotated
│   │   │   ├── Elaboration.lean
│   │   │   ├── Substitution.lean
│   │   │   ├── Syntax.lean
│   │   │   └── Weakening.lean
│   │   ├── checked
│   │   │   ├── Elaboration.lean
│   │   │   ├── Examples.lean
│   │   │   ├── IntroCtx.lean
│   │   │   ├── ManualProofExamples.lean
│   │   │   └── TypeChecker.lean
```
A short summary of the contents for each file:
- `IMLTT.typed.annotated.Syntax`: Definition of annotated term type `ATm n`
- `IMLTT.typed.annotated.Weakening`: Use `IMLTT.untyped.Weakening` on `ATm n`
- `IMLTT.typed.annotated.Substitution`: Use `IMLTT.untyped.Substitution` on `ATm n`
- `IMLTT.typed.annotated.Elaboration`: Elaborate the `[atm|]` `[acx|ε]`
- `IMLTT.typed.checked.ManualProofExamples`: Manual typing proofs created for understanding
- `IMLTT.typed.checked.TypeChecker`: Proof-generating typechecker with unfinished normalization function
- `IMLTT.typed.checked.Elaboration`: Elaboration of `ttheorem` command for creating theorems of judgments
- `IMLTT.typed.checked.Examples`: Multitude of different examples of usage of the typechecker
- `IMLTT.typed.checked.IntroCtx`: Theorems to 'shift' judgments from empty context to arbitrary context