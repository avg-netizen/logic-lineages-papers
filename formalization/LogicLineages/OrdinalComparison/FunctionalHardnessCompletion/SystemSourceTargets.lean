module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemSourceTargets
open OriginalDomain SourceCollisionCompletion SourceClasses

def ValuationPreservingSystem : Prop := ∀ (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution (SignedPair.Context n)),
  OrdinalSolves s ρ ↔ ∃ σ : AdmissibleSubstitution (compileSystem s).context,
    Preserves (compileSystem s).original ρ σ ∧
    SourceAggregateCompletion.AllEqual (valuation σ) (compileSystem s).detectors

/-- Exact one-pattern source assembly. All alignment witnesses are fresh and
simultaneous, and the one original valuation is shared by every equation. -/
def SystemEquality : Prop := ∀ (n : Nat) (s : System n),
  (∃ ρ : AdmissibleSubstitution (SignedPair.Context n), OrdinalSolves s ρ) ↔
  ∃ ρ : AdmissibleSubstitution (compileSystem s).context,
    rawScalar (valuation ρ) (strictSystemPair s).1 =
      rawScalar (valuation ρ) (strictSystemPair s).2

def QueryComplements : Prop := ∀ (n : Nat) (s : System n),
  universalStrictSystem s ↔ ¬∃ ρ : AdmissibleSubstitution (SignedPair.Context n), OrdinalSolves s ρ

def WeakQueryComplements : Prop := ∀ (n : Nat) (s : System n),
  universalWeakSystem s ↔ ¬∃ ρ : AdmissibleSubstitution (SignedPair.Context n), OrdinalSolves s ρ

def LevelTwoBounds : Prop := ∀ (n : Nat) (s : System n),
  (∀ τ ∈ (compileSystem s).context, τ.level ≤ 1) ∧
  InternalLevelBound 2 (strictSystemPair s).1 ∧
  InternalLevelBound 2 (strictSystemPair s).2 ∧
  InternalLevelBound 2 (weakSystemPair s).1 ∧
  InternalLevelBound 2 (weakSystemPair s).2

/-- Both finite-query clauses, still separate from undecidability. -/
def PolynomialQueryReduction : Prop := ∀ (n : Nat) (s : System n),
  (¬PolynomialSatisfiable s ↔ ∀ z ∈ masks n, universalStrictSystem (restrictSystem z s)) ∧
  (¬PolynomialSatisfiable s ↔ ∀ z ∈ masks n, universalWeakSystem (restrictSystem z s))

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemSourceTargets
