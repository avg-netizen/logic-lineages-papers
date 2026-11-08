module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosure
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- BOTH actual parameterized program graphs, at the SAME symbolic parameter.
The unchanged whole-state goodRunP accepts status one, empty work and exactly
one result, including zero. The raw foldP graph is not itself evidence of
success: its default zero is never substituted for the goodRunP graph.
Original state encoding, initial state and payload-based fuel are unchanged. -/
def certifiedFoldP {α : Type} (guard leaf : Program 2) (combine : Program 5)
    (out value parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (InternalParameterizedApplicationResultFoldCalibration.goodRunP guard leaf combine)
      InternalOriginalStepGuard.one value parameter ⊓
    graph2 (InternalParameterizedApplicationResultStack.foldP guard leaf combine)
      out value parameter

/-- The two actual fallback graphs on the WHOLE original packed input at
one parameter. The existing openGuardP includes the original tag-two test
and exact-one root guard. No validity, successful-run, payload/output bound
or nonzero-output premise is included. -/
def leafGraphsP {α : Type} (guard leaf : Program 2)
    (out value parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (InternalParameterizedApplicationResultStack.openGuardP guard)
      OrdinaryArithmetic.zeroTerm value parameter ⊓
    graph2 leaf out value parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosure
