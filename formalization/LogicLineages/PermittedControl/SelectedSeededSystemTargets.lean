module
public import LogicLineages.PermittedControl.SelectedSeededSystemDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededSystemTargets
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector Source.AdmissibleSum
open Source.FunctionalHardnessCompletion SelectedSeededSystem

def ValuationPreservation : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)),
  Solves ctrl s ρ ↔ ∃ σ : AdmissibleSubstitution ctrl (SeededSystem.compile s).context,
    SelectedSystemReduction.Preserves ctrl (SeededSystem.compile s).original ρ σ ∧
    SelectedAggregation.AllEqual ctrl policy σ (SeededSystem.compile s).detectors

def SystemEquality : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (n : Nat) (s : System n),
  PolynomialSatisfiable s ↔ ∃ σ : AdmissibleSubstitution ctrl (SeededSystem.compile s).context,
    groundValue ctrl policy σ (SeededSystem.strictPair s).1=
      groundValue ctrl policy σ (SeededSystem.strictPair s).2

def QueryComplements : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (n : Nat) (s : System n),
  (universalStrict ctrl policy s ↔ ¬PolynomialSatisfiable s) ∧
  (universalWeak ctrl policy s ↔ ¬PolynomialSatisfiable s)

def SuccessfulQueries : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution ctrl (SeededSystem.compile s).context),
  SelectedAggregation.GroundResult ctrl policy ρ (SeededSystem.strictPair s).1 ∧
  SelectedAggregation.GroundResult ctrl policy ρ (SeededSystem.strictPair s).2 ∧
  SelectedAggregation.GroundResult ctrl policy ρ (SeededSystem.weakPair s).1 ∧
  SelectedAggregation.GroundResult ctrl policy ρ (SeededSystem.weakPair s).2

def LevelThreeBounds : Prop := ∀ (n : Nat) (s : System n),
  (∀ τ ∈ (SeededSystem.compile s).context, τ.level≤1) ∧
  SourceClasses.InternalLevelBound 3 (SeededSystem.strictPair s).1 ∧
  SourceClasses.InternalLevelBound 3 (SeededSystem.strictPair s).2 ∧
  SourceClasses.InternalLevelBound 3 (SeededSystem.weakPair s).1 ∧
  SourceClasses.InternalLevelBound 3 (SeededSystem.weakPair s).2

/-- Empty fold and printed augmentation have the same satisfiability and false universal queries. -/
def EmptySourceCorrespondence : Prop :=
  (∀ n (s : System n), PolynomialSatisfiable (augmentEmpty s) ↔ PolynomialSatisfiable s) ∧
  ∀ ctrl K, SelectedWithThreshold ctrl K → ∀ (policy : Policy) (n : Nat),
    (∀ ρ : AdmissibleSubstitution ctrl (SignedPair.Context n),
      groundValue ctrl policy ρ (SeededSystem.strictPair ([] : System n)).1=1 ∧
      groundValue ctrl policy ρ (SeededSystem.strictPair ([] : System n)).2=1) ∧
    ¬universalStrict ctrl policy ([] : System n) ∧
    ¬universalWeak ctrl policy ([] : System n) ∧
    ¬universalStrict ctrl policy [zeroEquation n] ∧
    ¬universalWeak ctrl policy [zeroEquation n]

def SelectedSeededSystem : Prop := ValuationPreservation ∧ SystemEquality ∧
  QueryComplements ∧ SuccessfulQueries ∧ LevelThreeBounds ∧ EmptySourceCorrespondence
end LogicLineages.PermittedControl.SelectedSeededSystemTargets
