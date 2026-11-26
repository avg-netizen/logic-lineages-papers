module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdge
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Retain the complete original quotient inversion and the requested
actualJ decomposition. Component equalities identify its canonical function
and argument with the requested function and that requested raw argument's
actual fold. The SAME child quotient edge and target actualJ retain the
original child certificate, requested raw argument and symbolic parameter. -/
def Recovered {alpha : Type} (data : Data) (oldStep : Program 4)
    (arrow d e function argument x y certificate parameter
      S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument argumentOut : OTerm alpha) : Formula alpha :=
  OriginalNeutralQuotient.Recovered data oldStep x y certificate parameter
      S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument ⊓
    (OriginalNeutralApplication.Recovered data d e function argument x argumentOut parameter ⊓
      (equal rawD d ⊓
        (equal rawE e ⊓
          (equal functionOut function ⊓
            (equal canonicalArgument argumentOut ⊓
              (edgeAccepted data oldStep function targetFunctionOut child parameter ⊓
                (InternalOriginalUniformApplicationTyping.typedGraph
                    data targetFunctionOut arrow parameter ⊓
                  InternalParameterizedCanonicalResultFold.applicationGraph
                    data y d e targetFunctionOut argument parameter)))))))

/-- Original neutral application-edge inversion with the requested function
and raw argument retained literally. Only the original typed input premises,
actualJ graph, canonical neutrality and actual quotient edge are inputs.
All raw witnesses, component equalities, child edge and target application
are conclusions obtained internally. -/
def NeutralApplicationEdges (data : Data) (window : Program 1) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (arrow d e function argument x y certificate parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma
    (OriginalNeutralApplication.InputPremises data window arrow d e function argument parameter)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedCanonicalResultFold.applicationGraph data x d e function argument parameter)) →
  Nonempty (Derivation body Gamma
    (graph1 OriginalNeutralLeaf.neutralTest InternalOriginalStepGuard.one x)) →
  Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter)) →
  Nonempty (Derivation body (graph1 BottomRepresentative.bottomCode y e :: Gamma) psi) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument argumentOut : OTerm beta,
    Nonempty (Derivation body Delta
      (Recovered data oldStep (arrow.relabel j) (d.relabel j) (e.relabel j)
        (function.relabel j) (argument.relabel j) (x.relabel j) (y.relabel j)
        (certificate.relabel j) (parameter.relabel j)
        S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
        functionOut targetFunctionOut canonicalArgument argumentOut)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdge
