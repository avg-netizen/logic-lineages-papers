module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch constantZero)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatch (constant)
open NumberedWindowInternalAtomicRefinement (freeSource bottomSource)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)

/-- A transparent arithmetic front end to the chosen original raw rank.
The two exact bare atom branches allow open ID1 reports without reflecting
the selected raw numerical evaluator. The nested case reads the actual
raw least field, not a caller-supplied representative. -/
def addressRank (raw : Program 1) : Program 1 :=
  branch freeSource
    (branch bottomSource (branch addressGood (constantZero 1) (applyUnary raw rawLeast))
      (constant 1 1))
    (constant 1 2)

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRank
