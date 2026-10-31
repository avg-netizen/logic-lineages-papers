module
public import LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearchDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearch.Targets
/-- Generic supplier only: no assertion that a particular source evaluator is computable. -/
def ComplementEnumerable : Prop := ∀ bad : Nat → Nat → Bool,
  Computable₂ bad → REPred (fun q => ¬ Good bad q)
def DecisionIffBound : Prop := ∀ bad : Nat → Nat → Bool,
  Computable₂ bad → (ComputablePred (Good bad) ↔ HasComputableBound bad)
def PrefixComputable : Prop := ∀ bad : Nat → Nat → Bool,
  Computable₂ bad → Computable₂ (prefixBad bad)
def PrefixCorrect : Prop := ∀ (bad : Nat → Nat → Bool) q n,
  prefixBad bad q n = true ↔ ∃ r ≤ n, bad q r = true
end LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearch.Targets
