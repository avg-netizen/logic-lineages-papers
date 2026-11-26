module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPath
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The first entry of the ORIGINAL positive-path code, its exact encoded
vertex/certificate pair, its literal uniform quotient edge and the unchanged
ordinary suffix. The endpoint y is not assigned an application shape. -/
def FirstStep {alpha : Type} (data : Data) (oldStep : Program 4)
    (x y pathCode parameter raw tail vertex certificate : OTerm alpha) : Formula alpha :=
  graph2 InternalListCodec.consCode pathCode raw tail ⊓
    (graph2 InternalPairing.pairing raw vertex certificate ⊓
      (edgeAccepted data oldStep x vertex certificate parameter ⊓
        InternalParameterizedPathChecker.pathGraph (edgeChecker data oldStep)
          vertex y tail parameter))

/-- Positive acceptance alone supplies the first edge and its original
reflexive suffix, including both original code-constructor equations. -/
def FirstStepCases (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (x y pathCode parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma
    (InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep)
      x y pathCode parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ raw tail vertex certificate : OTerm beta,
    Nonempty (Derivation body Delta
      (FirstStep data oldStep (x.relabel j) (y.relabel j)
        (pathCode.relabel j) (parameter.relabel j) raw tail vertex certificate)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

/-- Invert only the FIRST edge of the original positive path out of the
requested non-lambda application. Both cases retain its exact original code
and suffix. A later function reduct may be a lambda and beta may change the
final endpoint's shape; no conclusion excludes those original reductions. -/
def NonLambdaApplicationPositivePaths (data : Data) (window : Program 1)
    (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (arrow d e function argument x y pathCode parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma
    (OriginalNeutralApplication.InputPremises data window arrow d e function argument parameter)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedCanonicalResultFold.applicationGraph data x d e function argument parameter)) →
  Nonempty (Derivation body Gamma (OriginalNonLambdaApplication.nonLambda function)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep)
      x y pathCode parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ raw tail vertex certificate : OTerm beta,
    Nonempty (Derivation body Delta
      (FirstStep data oldStep (x.relabel j) (y.relabel j)
        (pathCode.relabel j) (parameter.relabel j) raw tail vertex certificate)) →
    Nonempty (Derivation body
      (graph1 BottomRepresentative.bottomCode vertex (e.relabel j) :: Delta) (psi.relabel j))) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ raw tail vertex certificate : OTerm beta,
    Nonempty (Derivation body Delta
      (FirstStep data oldStep (x.relabel j) (y.relabel j)
        (pathCode.relabel j) (parameter.relabel j) raw tail vertex certificate)) →
    ∀ S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument argumentOut : OTerm beta,
    Nonempty (Derivation body Delta
      (OriginalNeutralApplicationEdge.Recovered data oldStep
        (arrow.relabel j) (d.relabel j) (e.relabel j) (function.relabel j)
        (argument.relabel j) (x.relabel j) vertex certificate (parameter.relabel j)
        S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
        functionOut targetFunctionOut canonicalArgument argumentOut)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPath
