# imltt_in_lean

This fork builds upon the implementation of syntactic properties of an intensional Martin-Löf type theory and embeds it as a domain-specific language in Lean for writing terms and judgments. 
This custom 'frontend' includes named variables instead of de Bruijn indices, localized error messages, and the ability to use global constants across terms.
Furthermore, parts of a proof-generating typechecker are implemented and used to automatically create Lean theorems for expressed judgments.