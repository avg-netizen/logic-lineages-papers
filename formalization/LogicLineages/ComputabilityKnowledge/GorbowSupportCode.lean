module

public import LogicLineages.ComputabilityKnowledge.GorbowFreeSupport
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation

@[expose] public section

/-! Effective free support by observing awaited variable tokens in the literal
scanner. Rank context-index is binder-invariant. Queries require i<ambient n,
so bound indices (whose rank exceeds ambient n) are not reported as free. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSupportCode
open GorbowSyntax GorbowSyntaxValidation
abbrev ObservedState := State × Bool

def sees (rank : Nat) (state : State) (token : Nat) : Bool :=
  match state with
  | some (task :: _) => decide (task.1 = 2 ∧ token < task.2 ∧ task.2 - token = rank)
  | _ => false

def observeStep (rank : Nat) (s : ObservedState) (token : Nat) : ObservedState :=
  (step s.1 token, s.2 || sees rank s.1 token)

def occurs (kind n i : Nat) (raw : List Nat) : Bool :=
  if i < n then ((raw.foldl (observeStep (n-i)) (some [(kind,n)], false)).2) else false

def termNames (n : Nat) (raw : List Nat) : Option (List Nat) :=
  if validTerm n raw then some ((List.range n).filter (fun i => occurs 0 n i raw)) else none

def formulaNames (n : Nat) (raw : List Nat) : Option (List Nat) :=
  if validFormula n raw then some ((List.range n).filter (fun i => occurs 1 n i raw)) else none

def selectorCode (raw : List Nat) : Bool := decide (formulaNames 1 raw = some [0])

def preciseTermCode (m n : Nat) (raw : List Nat) : Bool :=
  (termNames m raw).any (fun names => decide (names.length = n))

def preciseFormulaCode (m n : Nat) (raw : List Nat) : Bool :=
  (formulaNames m raw).any (fun names => decide (names.length = n))
end LogicLineages.ComputabilityKnowledge.GorbowSupportCode
