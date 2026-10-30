module
public import LogicLineages.OrdinalComparison.ControlDefinitions
public import LogicLineages.OrdinalComparison.BinaryDenominatorDefinitions
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Actual paper10 linked parameters. The budget is the fixed Phi, not an
independent large-number input. Natural subtractions are separately calibrated
by strict bounds in the targets. -/
def actualLinkedBudget (u : Nat) : Nat := Phi u
def actualLinkedBinaryExponent (u : Nat) : Nat := Nat.log 2 (actualLinkedBudget u)
def actualLinkedHalfExponent (u : Nat) : Nat := actualLinkedBinaryExponent u - 1
def actualLinkedModulus (u : Nat) : Nat := 2 ^ actualLinkedHalfExponent u + 1
def actualLinkedTail (u : Nat) : Nat := u - 2
def actualLinkedDegree (u : Nat) : Nat := actualBinarySourceDimension (actualLinkedTail u)
def actualLinkedOffset (u : Nat) : Nat := u - 4
def actualLinkedCutoff (u : Nat) : Nat := actualLinkedBudget u - u + 3

end LogicLineages.OrdinalComparison
