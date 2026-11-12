module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Adapt the existing ORIGINAL edge-code selectors to runtime four-vectors.
No new source/target encoding is introduced. -/
def edge : Program 4 := .composition edgeCode ![.projection 0,.projection 1,.projection 2]
def atEdge (selector : Program 1) : Program 4 := .composition selector (fun _ : Fin 1 => edge)
def sourceFunction : Program 4 := atEdge InternalApplicationStepPeel.functionCode
def targetFunction : Program 4 := atEdge InternalApplicationStepPeel.targetFunctionCode
def childCertificate : Program 4 := atEdge InternalApplicationStepPeel.peeledStep
def childParameter : Program 4 := .projection 3
/-- Existing structuralGuard checks both app tags, outer codomain/domain,
identical argument payload, and the genuine nonempty appFunction path. -/
def structuralGuard : Program 4 := atEdge InternalApplicationStepPeel.structuralGuard
def hopGuard (source : Program 2) : Program 4 :=
 InternalAcceptance.conjunction (OriginalTransparentVariableStep.sourceAt source) structuralGuard
def childLive : Program 4 := .composition OriginalHereditaryLambda.live
 ![sourceFunction,targetFunction,childCertificate,childParameter]
/-- A reusable SINGLE hop. Every failed guard preserves the entire state.
This is not a mixed path normalizer and is not inserted into any global tuple. -/
def transition (source : Program 2) : Program 1 :=
 InternalAcceptance.branch
  (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
   (OriginalHereditaryLambda.atState (hopGuard source)))
  (.projection 0) (OriginalHereditaryLambda.atState childLive)
def oneStep (source : Program 2) (oldStep : Program 4) : Program 4 :=
 .composition (OriginalHereditaryLambda.atState oldStep)
  (fun _ : Fin 1 => .composition (transition source)
   (fun _ : Fin 1 => OriginalHereditaryLambda.live))
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
 {p with oldStep := oneStep p.base.oldSource p.oldStep}

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionDefinitions
