module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
/-- Literal dispatcher only. Empty/unknown frames preserve all state; supported
frame tags delegate to the separately checked visit and return Programs. -/
def work : Program 1 := leftOf (.projection 0)
def frame : Program 1 := .composition InternalListCodec.headCode (fun _ : Fin 1 => work)
def step (R : Program 2) : Program 1 := InternalAcceptance.branch work (.projection 0)
  (OriginalTypedDecoder.ifSame (leftOf frame) (constant 1 0) OriginalHereditaryAnnotatedVisit.step
    (OriginalTypedDecoder.ifSame (leftOf frame) (constant 1 1)
      (OriginalHereditaryReturnStep.step R) (.projection 0)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStep
