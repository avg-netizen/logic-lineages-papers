module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.UndecidabilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision

/-- Finite conjunction of actual Boolean answers. An empty query list returns
true, exactly as the finite universal quantifier in FiniteQueryReduction. -/
def allAnswers (answer : Nat → Bool) (queries : List Nat) : Bool :=
  queries.foldr (fun q previous => answer q && previous) true

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision
