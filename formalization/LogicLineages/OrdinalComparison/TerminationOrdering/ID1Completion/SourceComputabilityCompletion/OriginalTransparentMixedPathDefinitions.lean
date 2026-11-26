module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exactly ONE hop. Lambda success takes its original child state; otherwise
only the application-function transition runs. No sequential double hop. -/
def transition (source : Program 2) : Program 1 :=
 InternalAcceptance.branch
  (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
   (OriginalHereditaryLambda.atState (OriginalTransparentLambdaStep.hopGuard source)))
  (OriginalTransparentApplicationFunctionDefinitions.transition source)
  (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive)
/-- Iterate over the ORIGINAL raw certificate path, without new fuel. -/
def run (source : Program 2) : Program 4 :=
 .composition (InternalRawListRepeat.repeatProgram (transition source))
  ![OriginalHereditaryLambda.path,OriginalHereditaryLambda.live]
def refined (source : Program 2) (oldStep : Program 4) : Program 4 :=
 .composition (OriginalHereditaryLambda.atState oldStep) (fun _ : Fin 1 => run source)
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
 {p with oldStep := refined p.base.oldSource p.oldStep}

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathDefinitions
