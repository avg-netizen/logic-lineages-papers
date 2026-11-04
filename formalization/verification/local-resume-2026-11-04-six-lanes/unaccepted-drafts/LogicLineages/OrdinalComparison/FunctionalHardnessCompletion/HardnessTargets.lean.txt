module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessTargets

/-- Whole hardness.tex thm:functional-hardness. This pending target retains
the broad printed source domain, both weak/strict undecidability assertions,
and both actual level-three computable single-query reductions. The level-two
finite-query construction and genuine source undecidability supplier must be
proved, not assumed, before this proposition can be inhabited. -/
def FullFunctionalHardness : Prop :=
  (¬HasComparisonDecider 2 true) ∧ (¬HasComparisonDecider 2 false) ∧
    FiniteQueryReduction true ∧ FiniteQueryReduction false ∧
    SingleQueryReduction true ∧ SingleQueryReduction false

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessTargets
