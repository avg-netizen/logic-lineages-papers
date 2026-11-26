module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeTargets (goodState)
open NumberedWindowInternalSparseRawRun (initialState iterateState ownState)

/-- The reachable shape is preserved by the actual raw recursor at
arbitrary open fuel. The original start is an unchanged parameter that
carries the shape as an explicit object premise; it is not imposed on an
arbitrary start, and the supplied output is an arbitrary open term. -/
def ExactOpenRawLoopShape : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (fuel start out : OTerm α),
    Nonempty (Derivation body [] ((goodState start).imp
      ((programGraph (iterateState p other) out ![fuel,start]).imp (goodState out))))

/-- Genuine object graph of the actual initial scratch at an arbitrary
open tape: flag zero and frame the successor of the ordered raw triple. -/
def ExactOpenInitialState : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (q w r : OTerm α),
    Nonempty (Derivation body []
      (programGraph initialState (stateTerm z (frameValueTerm q w r)) ![q,w,r]))

/-- Every supplied output of the actual own-witness state program on an
arbitrary open tape has the reachable shape. No premise on the tape. -/
def ExactOpenOwnStateShape : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (q w r out : OTerm α),
    Nonempty (Derivation body []
      ((programGraph (ownState p other) out ![q,w,r]).imp (goodState out)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeTargets
