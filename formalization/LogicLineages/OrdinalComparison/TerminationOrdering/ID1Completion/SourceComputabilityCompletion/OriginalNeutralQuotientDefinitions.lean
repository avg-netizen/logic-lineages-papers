module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityStepTransferTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniformStepQuotientTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotient
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open ClaudeSupervisedCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original quotient certificate and its raw fields are retained with
the full peeled application step. Its SAME child edgeCode is accepted by the
literal UniformCertificateCompletion quotient checker at the internally
recovered canonical child outputs. The raw argument and its one actual fold
are shared by both canonical application constructors. -/
def Recovered {alpha : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter S T K state d e arrow f g a k child
      functionOut targetFunctionOut argumentOut : OTerm alpha) : Formula alpha :=
  selectors certificate S T K ⊓
    (requirements data oldStep x y S T K parameter ⊓
      (graph3 edgeCode state S T K ⊓
        (InverseGuardTargets.Peeled
            (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
            oldStep d e arrow f g a k child InternalOriginalStepGuard.one state S T K parameter ⊓
          (OriginalUniformStepQuotientTargets.Recovered data oldStep f g k
              functionOut targetFunctionOut child parameter ⊓
            (InternalParameterizedCanonicalResultFold.foldGraph data argumentOut a parameter ⊓
              (graph4 application x d e functionOut argumentOut ⊓
                graph4 application y d e targetFunctionOut argumentOut))))))

/-- Original neutral quotient-edge inversion at one literal Data/window/step
tuple. All raw certificate fields, application witnesses and canonical child
outputs are obtained internally. The two alternatives are the literal
same-type bottom or a recovered SAME-checker function-child quotient edge.
No full-fold fixedness or externally requested component alignment is assumed. -/
def NeutralQuotientEdges (data : Data) (window : Program 1) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (x y certificate parameter typeCode : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma
    (OriginalFunctionNeutrality.windowGraph window x parameter)) →
  Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter)) →
  Nonempty (Derivation body Gamma
    (graph1 OriginalNeutralLeaf.neutralTest InternalOriginalStepGuard.one x)) →
  Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode x)) →
  Nonempty (Derivation body (graph1 BottomRepresentative.bottomCode y typeCode :: Gamma) psi) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ S T K state d e arrow f g a k child functionOut targetFunctionOut argumentOut : OTerm beta,
    Nonempty (Derivation body Delta
      (Recovered data oldStep (x.relabel j) (y.relabel j)
        (certificate.relabel j) (parameter.relabel j)
        S T K state d e arrow f g a k child functionOut targetFunctionOut argumentOut)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotient
