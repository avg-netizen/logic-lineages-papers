module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementASTProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
open NumberedWindowInternalNeutralAuxiliaryRefinement
open NumberedWindowInternalAtomicRefinement (atSource atTarget bottomTarget)
open NumberedWindowInternalAuxBottomRefinement (refineAuxBottom)

theorem exact_NeutralPositiveAST (i : Program 1) (r : Program 3) :
    neutralPositive i r = branch (atSource freeAux) (refineAuxBottom i r)
      (conjunction r (freeAuxTarget i)) := rfl

theorem exact_NeutralAuxTargetAST (i : Program 1) :
    freeAuxTarget i = branch bottomTarget bottomAuxTarget (conjunction bottomTarget (atTarget i)) := rfl

#print axioms exact_NeutralPositiveAST
#print axioms exact_NeutralAuxTargetAST
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementASTProof
