import Lean

open Lean Lean.Elab Command

inductive Even : Nat → Prop
  | zero : Even 0
  | succ : Even n → Even (n + 2)

inductive MyOption (α : Type) where
  | none : MyOption α
  | some : α → MyOption α
deriving Repr, ToExpr

#reduce Lean.toExpr (MyOption.some 42)

def is_even : (n : Nat) -> Option <| PLift <| Even n
  | 0 => pure <| .up Even.zero
  | 1 => none
  | n + 2 => do
    return .up <| Even.succ (← is_even n).down

example : Even 100 := ((is_even _).get (by decide)).down

elab "#is_even " n:num : command => do
  match is_even n.getNat with
  | some _ => logInfo s!"'{n.getNat} is even by proof'"
  | none => logInfo s!"'{n.getNat} is not even'"

#is_even 42
#is_even 57

syntax "close_even" : tactic

macro_rules
| `(tactic| close_even) => `(tactic| exact ((is_even _).get (by decide)).down)

def my42 : Nat := 42

example : Even 42 := by close_even

declare_syntax_cat ev (behavior := both)

syntax "E" num : ev
syntax "E" term : ev
syntax "EP" num : ev

syntax ">>" ev "<<" : term

def add (a b : Nat) : Nat := a + b

macro_rules
  | `(>> E $t:term <<) => `(Even (add $t 3))

elab_rules : term
  | `(>> E $t:term <<) => do
    let mysyn ← `(Even $t)
    let out ← Term.elabTerm mysyn.raw none
    logInfo s!"elaborated to {out}"
    Term.elabTerm mysyn.raw none
elab_rules : term
  | `(>> E $n:num <<) => do
    let mysyn ← `(Even $n)
    let out ← Term.elabTerm mysyn.raw none
    logInfo s!"elaborated to {out}"
    Term.elabTerm mysyn.raw none
elab_rules : term
  | `(>> EP $n:num <<) => do
    let mysyn ← `(Even (add $n 1))
    Term.elabTerm mysyn.raw none

#reduce >> EP 42 <<

example : >> E 48 << := by close_even
theorem yay : >> E my42 << := by close_even
#print yay
theorem ev12 : >> EP 11 << := by close_even

#check ev12
