module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundAlternativeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundStabilityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundChargeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalThinRoundAlternativeTargets (budgetStep)

/-- Formula-only finite potential: membership stabilizes, or elapsed
and remaining original uncovered occurrences fit the actual allowance. -/
def budget {α : Type} (elapsed initial remaining out next : OTerm α) : Formula α :=
  NumberedWindowInternalScratchInclusionThinProof.included next out ⊔
    NumberedWindowInternalThinUncoveredCount.bounded (OrdinaryArithmetic.addTerm elapsed remaining) initial

/-- One actual successor of the original filtered iteration preserves the
finite-descent budget, using the true count of the same vertices in a and b. -/
def ExactRoundCharge : Prop :=
  ExactRetainedPredecessor → NumberedWindowInternalThinUncoveredCountTargets.InternalStrictDecrease →
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed i a b c initial countA countB : OTerm α),
    let runs := budgetStep E vertices ctx ty seed i a b countA countB ⊓
      roundGraph E c (suc (suc i)) vertices ctx ty seed
    Nonempty (Derivation body Γ ((runs ⊓ budget i initial countA a b).imp
      (budget (suc i) initial countB b c)))

end LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundChargeTargets
