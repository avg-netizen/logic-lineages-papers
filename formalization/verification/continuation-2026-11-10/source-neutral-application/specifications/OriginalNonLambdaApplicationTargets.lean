module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open OriginalNonLambdaApplication

/-- On the SAME final globally selectable tuple, the original non-lambda
premise at the requested function implies neutrality of its actualJ output.
The original typed input facts suffice; the function tag and argument fold
are bound internally, and the requested RAW argument remains literal. -/
def ActualOriginalNonLambdaApplicationNeutrality : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (arrow d e function argument out parameter : OTerm alpha),
  Nonempty (Derivation body Gamma
    (OriginalNeutralApplication.InputPremises data r.window arrow d e function argument parameter)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedCanonicalResultFold.applicationGraph data out d e function argument parameter)) →
  Nonempty (Derivation body Gamma (nonLambda function)) →
  Nonempty (Derivation body Gamma
    (graph1 OriginalNeutralLeaf.neutralTest InternalOriginalStepGuard.one out))

/-- Replace the checked aligned ONE-edge eliminator's canonical application
neutrality premise with the original requested function's non-lambda graph.
The SAME quotient checker, raw argument, certificate, parameter, same-type
bottom and complete aligned recovered record remain unchanged. -/
def ActualOriginalNonLambdaApplicationEdgeElimination : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let r := OriginalApplicationSidecar.finalInputs p
  NonLambdaApplicationEdges (OuterSelection.data r.base r.window) r.window r.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationTargets
