module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitBridgeDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.NarendranTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear

/-- The natural triangular number is a witness, not a new input operation. -/
def triangularNat : Nat → Nat
  | 0 => 0
  | n+1 => triangularNat n+n

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear
