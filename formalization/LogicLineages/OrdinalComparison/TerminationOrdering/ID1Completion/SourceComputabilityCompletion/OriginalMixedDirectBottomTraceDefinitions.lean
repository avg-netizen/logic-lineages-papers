module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTrace
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Only original lambda-prefix or application-function-prefix provenance is inspected. No erasure, rank, observer equality, or desired transport result is tested. -/
def lambdaHop (source : Program 2) (leaf : Program 4) : Program 4 :=
 InternalAcceptance.conjunction (OriginalTransparentLambdaStep.hopGuard source) leaf
def applicationHop (source : Program 2) (leaf : Program 4) : Program 4 :=
 InternalAcceptance.conjunction (OriginalTransparentApplicationFunctionDefinitions.hopGuard source) leaf
/-- Exactly one selected successful hop. Every guard failure returns absorbing zero; unlike the calibration normalizer this recognizer may reject valid other source rules. -/
def transition (source : Program 2) (leaf : Program 4) : Program 1 :=
 InternalAcceptance.branch (.projection 0) (InternalAcceptance.constantZero 1)
  (InternalAcceptance.branch
   (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
    (OriginalHereditaryLambda.atState (lambdaHop source leaf)))
   (InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
     (OriginalHereditaryLambda.atState (applicationHop source leaf)))
    (InternalAcceptance.constantZero 1)
    (OriginalHereditaryLambda.atState OriginalTransparentApplicationFunctionDefinitions.childLive))
   (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive))
/-- Genuine old nil/direct-bottom certificate, old source, and SAME leaf. -/
def terminal (source : Program 2) (leaf : Program 4) : Program 4 :=
 OriginalLambdaDirectBottomTrace.terminal source leaf
def finish (source : Program 2) (leaf : Program 4) : Program 1 :=
 InternalAcceptance.branch (.projection 0) (InternalAcceptance.constantZero 1)
  (OriginalHereditaryLambda.atState (terminal source leaf))
def run (source : Program 2) (leaf : Program 4) : Program 4 :=
 .composition (InternalRawListRepeat.repeatProgram (transition source leaf))
  ![OriginalHereditaryLambda.path,OriginalHereditaryLambda.live]
def recognizes (source : Program 2) (leaf : Program 4) : Program 4 :=
 .composition (finish source leaf) (fun _ : Fin 1 => run source leaf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTrace
