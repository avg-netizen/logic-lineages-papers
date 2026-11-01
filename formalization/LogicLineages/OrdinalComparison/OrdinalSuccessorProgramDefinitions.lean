module
public import LogicLineages.OrdinalComparison.RawSplitDefinitions
public import LogicLineages.OrdinalComparison.EncodedFiniteTailDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- The actual raw finite remainder from the existing faithful split program. -/
def encodedOrdinalFiniteRemainder (eta : Nat) : Nat := (rawSplitCode eta).unpair.2

/-- Actual ordinary predecessor when the finite remainder is positive.
The total malformed/limit convention is not used as a source predecessor. -/
def encodedOrdinalSuccessorPredecessor (eta : Nat) : Nat :=
  let p := (rawSplitCode eta).unpair
  encodedFiniteTail p.1 (p.2-1)

end LogicLineages.OrdinalComparison
