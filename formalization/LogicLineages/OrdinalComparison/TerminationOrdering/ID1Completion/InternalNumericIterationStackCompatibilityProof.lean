module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationStackCompatibilityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The generic supplier is definitionally the already frozen concrete
numeric stack iterator, not merely extensionally equivalent in the model. -/
theorem stackIteration (node leaf : Program 1) :
    InternalNumericIteration.repeatProgram (InternalApplicationValidityStack.transition node leaf) =
      InternalApplicationValidityStack.iterate node leaf := rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationStackCompatibilityProof
