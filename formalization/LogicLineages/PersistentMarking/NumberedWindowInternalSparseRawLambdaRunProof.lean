module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaTickProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderTransitivity)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z)
open NumberedWindowInternalSparseRawRunLiftOwnProof (headLess tailLess ownRunLift)
open NumberedWindowInternalSparseRawLambdaFrame (witnessTerm liftedTape)
open NumberedWindowInternalSparseRawLambdaRun
open NumberedWindowInternalSparseRawLambdaTickProof (exact_OpenLambdaContextTick)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenLambdaWitnessStrict (child : OTerm α) :
    Nonempty (Derivation B Γ (ltF child (witnessTerm child))) := by
  let inner := rawCons child z
  obtain ⟨one⟩ := headLess (body := B) (Γ := Γ) child z
  obtain ⟨two⟩ : Nonempty (Derivation B Γ (ltF inner (witnessTerm child))) :=
    tailLess (numeral 1) inner
  exact closedApply (actualOriginalOrderTransitivity B α child inner (witnessTerm child))
    ⟨Derivation.conjunctionIntroduction one two⟩

/-- Both tapes run through the very same selected callback with its
original physical fuel. This is not a typed-window or least theorem. -/
theorem exact_OpenLambdaOwnRunLift : ExactOpenLambdaOwnRunLift := by
  intro B p other α Γ dom src child dst k
  dsimp only
  intro held
  exact ownRunLift p (lambdaFallback other) k (liftedTape dom src child dst) ![src,child,dst]
    (exact_OpenLambdaContextTick B p other α Γ z dom src child dst)
    (exact_OpenLambdaWitnessStrict child) held

#print axioms exact_OpenLambdaWitnessStrict
#print axioms exact_OpenLambdaOwnRunLift
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunProof
