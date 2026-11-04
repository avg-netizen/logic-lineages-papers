module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystem.Targets
open OriginalDomain SourceCollisionCompletion SourceClasses

def ExactValuationPreservation : Prop := ∀ (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution (SignedPair.Context n)),
  Solves s ρ ↔ ∃ σ : AdmissibleSubstitution (compile s).context,
    Preserves (compile s).original ρ σ ∧
    SourceAggregateCompletion.AllEqual (valuation σ) (compile s).detectors

/-- Whole-system equivalence with zero-valued polynomial unknowns allowed.
Exactly one compiled source pair is used, including the empty input system. -/
def ExactSystemEquality : Prop := ∀ (n : Nat) (s : System n),
  PolynomialSatisfiable s ↔ ∃ ρ : AdmissibleSubstitution (compile s).context,
    rawScalar (valuation ρ) (strictPair s).1=rawScalar (valuation ρ) (strictPair s).2

def ExactSingleQuerySemantics : Prop := ∀ (n : Nat) (s : System n),
  (universalStrict s ↔ ¬PolynomialSatisfiable s) ∧
  (universalWeak s ↔ ¬PolynomialSatisfiable s)

def ExactLevelThreeBounds : Prop := ∀ (n : Nat) (s : System n),
  (∀ τ∈(compile s).context,τ.level≤1) ∧
  InternalLevelBound 3 (strictPair s).1 ∧ InternalLevelBound 3 (strictPair s).2 ∧
  InternalLevelBound 3 (weakPair s).1 ∧ InternalLevelBound 3 (weakPair s).2

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystem.Targets
