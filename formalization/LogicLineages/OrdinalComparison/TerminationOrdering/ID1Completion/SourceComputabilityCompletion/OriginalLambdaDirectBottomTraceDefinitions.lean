module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTrace
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Restricted OLD-edge recognizer only; it does not alter the selected leaf.
No transformed edge, erasure, rank, or desired transport result is checked. -/
def hop (source : Program 2) (leaf : Program 4) : Program 4 :=
 InternalAcceptance.conjunction (OriginalTransparentLambdaStep.hopGuard source) leaf
/-- Failure is absorbing zero, unlike the calibration-preserving normalizer's
identity fallback. This separate recognizer deliberately recognizes a subset. -/
def transition (source : Program 2) (leaf : Program 4) : Program 1 :=
 InternalAcceptance.branch (.projection 0) (InternalAcceptance.constantZero 1)
  (InternalAcceptance.branch
   (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
    (OriginalHereditaryLambda.atState (hop source leaf)))
   (InternalAcceptance.constantZero 1)
   (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive))
/-- Terminal provenance is the original exact certificate constructor,
original source acceptance, and SAME existing leaf acceptance. -/
def terminal (source : Program 2) (leaf : Program 4) : Program 4 :=
 InternalAcceptance.conjunction (OriginalTransparentVariableStep.sourceAt source)
  (InternalAcceptance.conjunction leaf OriginalTransparentDirectBottom.active)
def finish (source : Program 2) (leaf : Program 4) : Program 1 :=
 InternalAcceptance.branch (.projection 0) (InternalAcceptance.constantZero 1)
  (OriginalHereditaryLambda.atState (terminal source leaf))
def run (source : Program 2) (leaf : Program 4) : Program 4 :=
 .composition (InternalRawListRepeat.repeatProgram (transition source leaf))
  ![OriginalHereditaryLambda.path,OriginalHereditaryLambda.live]
def recognizes (source : Program 2) (leaf : Program 4) : Program 4 :=
 .composition (finish source leaf) (fun _ : Fin 1 => run source leaf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTrace
