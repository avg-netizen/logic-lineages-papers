module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDecisionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision.Targets

def ConjunctionMeaning : Prop := ∀ (answer : Nat → Bool) (queries : List Nat),
  allAnswers answer queries=true ↔ ∀ q∈queries, answer q=true

def ConjunctionComputable : Prop := ∀ answer : Nat → Bool,
  Computable answer → Computable (allAnswers answer)

/-- A hypothetical decision program must answer only genuine source queries.
Every generated query is proved bounded. All answers true recognizes system
UNsatisfiability; complementation then decides satisfiability. -/
def FiniteQueryPullback : Prop := ∀ strict : Bool,
  FiniteQueryReduction strict → HasComparisonDecider 2 strict →
    ComputablePred encodedPolynomialSolvable

/-- Strict and weak are separate instances of the same verified finite-query
argument, not negations of one another on malformed or unbounded source terms. -/
def LevelTwoUndecidability : Prop :=
  (¬HasComparisonDecider 2 true) ∧ (¬HasComparisonDecider 2 false)

abbrev FullFunctionalHardness : Prop := HardnessTargets.FullFunctionalHardness

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision.Targets
