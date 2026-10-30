module

public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode
public import Mathlib.Computability.Primrec.List

@[expose] public section

/-! Literal prefix scanner. Task kind0 parses a term, kind1 a formula, kind2
an awaited variable index, each with its own current binder context. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation
open GorbowSyntax
abbrev Task := Nat × Nat
abbrev State := Option (List Task)

def expand (task : Task) (token : Nat) : State :=
  let n := task.2
  if task.1 = 0 then
    if token = 0 then some [(2,n)]
    else if token = 1 then some []
    else if token = 2 ∨ token = 5 then some [(0,n)]
    else if token = 3 ∨ token = 4 then some [(0,n),(0,n)]
    else none
  else if task.1 = 1 then
    if token = 0 ∨ token = 4 then some [(0,n),(0,n)]
    else if token = 1 ∨ token = 2 ∨ token = 3 ∨ token = 5 then some [(0,n)]
    else if token = 6 then some [(1,n)]
    else if token = 7 ∨ token = 8 ∨ token = 9 then some [(1,n),(1,n)]
    else if token = 10 ∨ token = 11 then some [(1,n+1)]
    else none
  else if task.1 = 2 then if token < n then some [] else none
  else none

def step (state : State) (token : Nat) : State := do
  let tasks ← state
  match tasks with
  | [] => none
  | task :: rest => do
      let added ← expand task token
      some (added ++ rest)

def scan (tasks : List Task) (raw : List Nat) : State := raw.foldl step (some tasks)

def validTerm (n : Nat) (raw : List Nat) : Bool := decide (scan [(0,n)] raw = some [])
def validFormula (n : Nat) (raw : List Nat) : Bool := decide (scan [(1,n)] raw = some [])

inductive StackMeaning : List Task → List Nat → Prop
  | nil : StackMeaning [] []
  | term {n tasks raw} (t : Term n) : StackMeaning tasks raw →
      StackMeaning ((0,n)::tasks) (GorbowTermPrefixCode.encode t ++ raw)
  | formula {n tasks raw} (φ : Formula n) : StackMeaning tasks raw →
      StackMeaning ((1,n)::tasks) (GorbowFormulaPrefixCode.encode φ ++ raw)
  | index {n tasks raw} (i : Nat) : i < n → StackMeaning tasks raw →
      StackMeaning ((2,n)::tasks) (i::raw)

end LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation
