module
public import LogicLineages.OrdinalComparison.EncodedMaximumDefinitions
public import LogicLineages.OrdinalComparison.RawSplitDefinitions

@[expose] public section

/-! Numeric literal replacement step for the closed-collapse procedure.
Finite states are absorbing because the procedure stops there. A nonfinite
state replaces its limit part by the exhaustive encoded maximum at Phi of
the original state's exact additive norm. -/

namespace LogicLineages.OrdinalComparison

def encodedFiniteTest (n : Nat) : Bool := decide ((rawSplitCode n).unpair.1 = 0)

def encodedFiniteValue (n : Nat) : Nat := (rawSplitCode n).unpair.2

def encodedDescentStep (n : Nat) : Nat :=
  if encodedFiniteTest n then n
  else encodedMaximumPredecessor (rawSplitCode n).unpair.1 (Phi (rawNormCode n))

def encodedStateAfter (n k : Nat) : Nat := (encodedDescentStep^[k]) n

end LogicLineages.OrdinalComparison
