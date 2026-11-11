module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplication
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Negate only the original packed function's constructor-tag graph at
lambda tag one. No replacement Program, decode, selected witness or
function-normalization assumption is introduced. -/
abbrev nonLambda {alpha : Type} (function : OTerm alpha) : Formula alpha :=
  (OriginalConstructorShape.tagGraph InternalOriginalStepGuard.one function).not

/-- The original requested non-lambda function supplies the neutral premise
for ONE literal uniform quotient edge out of its actualJ application. The
complete checked aligned recovered record is retained; the target function
is not asserted to remain non-lambda. This is not an inversion of H+ paths. -/
def NonLambdaApplicationEdges (data : Data) (window : Program 1) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (arrow d e function argument x y certificate parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma
    (OriginalNeutralApplication.InputPremises data window arrow d e function argument parameter)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedCanonicalResultFold.applicationGraph data x d e function argument parameter)) →
  Nonempty (Derivation body Gamma (nonLambda function)) →
  Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter)) →
  Nonempty (Derivation body (graph1 BottomRepresentative.bottomCode y e :: Gamma) psi) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument argumentOut : OTerm beta,
    Nonempty (Derivation body Delta
      (OriginalNeutralApplicationEdge.Recovered data oldStep
        (arrow.relabel j) (d.relabel j) (e.relabel j) (function.relabel j)
        (argument.relabel j) (x.relabel j) (y.relabel j)
        (certificate.relabel j) (parameter.relabel j)
        S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
        functionOut targetFunctionOut canonicalArgument argumentOut)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplication
