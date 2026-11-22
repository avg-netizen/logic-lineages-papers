module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundAlternativeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundStabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.Definitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseRoundAlternativeTargets (budgetStep)

/-- One actual successor of the original filtered iteration preserves the
finite-descent budget, using the true count of the same vertices in a and b. -/
def ExactRoundCharge : Prop :=
  ExactRetainedPredecessor → PrimaryUncoveredCount.Targets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed i a b c initial countA countB : OTerm α),
    let runs := budgetStep E vertices ctx ty seed i a b countA countB ⊓
      roundGraph E c (suc (suc i)) vertices ctx ty seed
    Nonempty (Derivation body Γ ((runs ⊓ PrimaryFiniteDescent.budget i initial countA a b).imp
      (PrimaryFiniteDescent.budget (suc i) initial countB b c)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeTargets
