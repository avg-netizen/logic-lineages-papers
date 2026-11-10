module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralStepTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityStepTransferTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open ClaudeSupervisedCompletion

/-- Reflect the neutrality of an actual canonical output back to the SAME
valid raw source, then eliminate its accepted original step. The source,
target, certificate, parameter, window, type and both continuations remain
literal. The result is raw same-type bottom or the full accepted function
child step; no equality of canonical application components is asserted. -/
def ActualOriginalFunctionNeutralityStepElimination : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let r := OriginalFunctionNeutrality.finalInputs p
  let data := OuterSelection.data r.base r.window
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (S T K out parameter typeCode : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma (stepAccepted data r.oldStep S T K parameter)) →
  Nonempty (Derivation body Gamma
    (graph2 (BottomRepresentative.windowAt r.window) InternalOriginalStepGuard.one S parameter)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedCanonicalResultFold.sourcePremises data S typeCode parameter)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedCanonicalResultFold.foldGraph data out S parameter)) →
  Nonempty (Derivation body Gamma
    (graph1 OriginalNeutralLeaf.neutralTest InternalOriginalStepGuard.one out)) →
  Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode S)) →
  Nonempty (Derivation body (graph1 BottomRepresentative.bottomCode T typeCode :: Gamma) psi) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ state d e arrow f g a k child : OTerm beta,
    Nonempty (Derivation body Delta
      (graph3 edgeCode state (S.relabel j) (T.relabel j) (K.relabel j) ⊓
        (InverseGuardTargets.Peeled (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
          r.oldStep d e arrow f g a k child InternalOriginalStepGuard.one state
          (S.relabel j) (T.relabel j) (K.relabel j) (parameter.relabel j) ⊓
            stepAccepted data r.oldStep f g k (parameter.relabel j)))) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityStepTransferTargets
