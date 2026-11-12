module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStep
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only independently supplied original source validity and literal lambda
shape/path tests. No oldStep, new checker or desired law enters this AST. -/
def hopGuard (source : Program 2) : Program 4 :=
  InternalAcceptance.conjunction (OriginalTransparentVariableStep.sourceAt source)
    (InternalAcceptance.conjunction OriginalLambdaGuardLeaf.sourceLambda
      (InternalAcceptance.conjunction OriginalLambdaGuardLeaf.matchingTarget
        OriginalHereditaryLambda.lamPath))

/-- On every failed guard retain the WHOLE original state, including all
four coordinates and malformed values. Successful hops use actual child
selectors, strip only the original path head, and extend the original Gamma. -/
def transition (source : Program 2) : Program 1 :=
  InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
      (OriginalHereditaryLambda.atState (hopGuard source)))
    (.projection 0)
    (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive)

/-- Bounded only by the original raw certificate list. No path reconstruction,
new fuel estimate, recursive Program definition, or hidden acceptance oracle. -/
def run (source : Program 2) : Program 4 :=
  .composition (InternalRawListRepeat.repeatProgram (transition source))
    ![OriginalHereditaryLambda.path,OriginalHereditaryLambda.live]

def refined (source : Program 2) (oldStep : Program 4) : Program 4 :=
  .composition (OriginalHereditaryLambda.atState oldStep)
    (fun _ : Fin 1 => run source)

def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined p.base.oldSource p.oldStep }

/-- Literal parent/child coordinates. Original constructor graphs, body type
selectors, certificate prefix and parameter pair/cons graphs are premises;
no hop/normalizer/guard success is supplied. Parent source membership stays
explicit because it cannot follow from child typing alone. -/
def LambdaHop {alpha : Type} (source : Program 2)
    (s t cert parameter childS childT childCert childParam d e context gamma extended : OTerm alpha) : Formula alpha :=
  graph2 source InternalOriginalStepGuard.one s parameter ⊓
    (graph3 OriginalLambdaConstructor.constructor s d e childS ⊓
      (graph3 OriginalLambdaConstructor.constructor t d e childT ⊓
        (graph1 InternalUnpair.left e childS ⊓
          (graph1 InternalUnpair.left e childT ⊓
            (graph1 OriginalHereditaryLambda.prefixCertificate cert childCert ⊓
              (graph2 InternalPairing.pairing parameter context gamma ⊓
                (graph2 InternalListCodec.consCode extended d gamma ⊓
                  graph2 InternalPairing.pairing childParam context extended)))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStep
