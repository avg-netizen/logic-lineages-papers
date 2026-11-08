module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosure
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The two actual leaf-branch graphs on the WHOLE original packed input.
The guard is the unchanged openGuard, including its original application-tag
check and exact-one root guard. No source validity, successful run, payload
bound, output bound or nonzero-output condition is part of this formula. -/
def leafGraphs {α : Type} (guard leaf : Program 1)
    (out value : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 (InternalApplicationResultStack.openGuard guard) OrdinaryArithmetic.zeroTerm value ⊓
    graph1 leaf out value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosure
