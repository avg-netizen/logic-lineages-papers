module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineState
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Auxiliary state constructors for the original machine, not a replacement
transition or graph. Inputs are [erased type, cutoff, raw, work suffix, stack]. -/
def visitState : Program 5 := liveOf
  (consOf (visitOf (.projection 0) (.projection 1) (.projection 2)) (.projection 3)) (.projection 4)

abbrev returnState := InternalApplicationResultStack.returnState
abbrev emptyState := InternalApplicationResultStack.emptyState
abbrev finishedState := OriginalLambdaTraversalInternal.finishedState


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineState
