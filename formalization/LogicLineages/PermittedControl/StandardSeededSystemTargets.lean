module
public import LogicLineages.PermittedControl.SelectedSeededSystemDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSeededSystem
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector Source.AdmissibleSum
open Source.FunctionalHardnessCompletion SelectedSeededSystem

/-- The same original valuation is retained in every compiled seeded equation,
at the unchanged displayed control Phi and for every genuine policy. -/
def ValuationPreservation : Prop :=
  ∀ (policy : Policy) (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution Phi (SignedPair.Context n)),
  Solves Phi s ρ ↔ ∃ σ : AdmissibleSubstitution Phi (SeededSystem.compile s).context,
    SelectedSystemReduction.Preserves Phi (SeededSystem.compile s).original ρ σ ∧
    SelectedAggregation.AllEqual Phi policy σ (SeededSystem.compile s).detectors

def SystemEquality : Prop :=
  ∀ (policy : Policy) (n : Nat) (s : System n),
  PolynomialSatisfiable s ↔ ∃ σ : AdmissibleSubstitution Phi (SeededSystem.compile s).context,
    groundValue Phi policy σ (SeededSystem.strictPair s).1=
      groundValue Phi policy σ (SeededSystem.strictPair s).2

def QueryComplements : Prop :=
  ∀ (policy : Policy) (n : Nat) (s : System n),
  (universalStrict Phi policy s ↔ ¬PolynomialSatisfiable s) ∧
  (universalWeak Phi policy s ↔ ¬PolynomialSatisfiable s)

def SuccessfulQueries : Prop :=
  ∀ (policy : Policy) (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution Phi (SeededSystem.compile s).context),
  SelectedAggregation.GroundResult Phi policy ρ (SeededSystem.strictPair s).1 ∧
  SelectedAggregation.GroundResult Phi policy ρ (SeededSystem.strictPair s).2 ∧
  SelectedAggregation.GroundResult Phi policy ρ (SeededSystem.weakPair s).1 ∧
  SelectedAggregation.GroundResult Phi policy ρ (SeededSystem.weakPair s).2

def LevelThreeBounds : Prop := ∀ (n : Nat) (s : System n),
  (∀ τ ∈ (SeededSystem.compile s).context, τ.level≤1) ∧
  SourceClasses.InternalLevelBound 3 (SeededSystem.strictPair s).1 ∧
  SourceClasses.InternalLevelBound 3 (SeededSystem.strictPair s).2 ∧
  SourceClasses.InternalLevelBound 3 (SeededSystem.weakPair s).1 ∧
  SourceClasses.InternalLevelBound 3 (SeededSystem.weakPair s).2

/-- Empty fold and printed augmentation have the same satisfiability and false universal queries. -/
def EmptySourceCorrespondence : Prop :=
  (∀ n (s : System n), PolynomialSatisfiable (augmentEmpty s) ↔ PolynomialSatisfiable s) ∧
  ∀ (policy : Policy) (n : Nat),
    (∀ ρ : AdmissibleSubstitution Phi (SignedPair.Context n),
      groundValue Phi policy ρ (SeededSystem.strictPair ([] : System n)).1=1 ∧
      groundValue Phi policy ρ (SeededSystem.strictPair ([] : System n)).2=1) ∧
    ¬universalStrict Phi policy ([] : System n) ∧
    ¬universalWeak Phi policy ([] : System n) ∧
    ¬universalStrict Phi policy [zeroEquation n] ∧
    ¬universalWeak Phi policy [zeroEquation n]

def StandardSeededSystem : Prop := ValuationPreservation ∧ SystemEquality ∧
  QueryComplements ∧ SuccessfulQueries ∧ LevelThreeBounds ∧ EmptySourceCorrespondence
end LogicLineages.PermittedControl.StandardSeededSystem
