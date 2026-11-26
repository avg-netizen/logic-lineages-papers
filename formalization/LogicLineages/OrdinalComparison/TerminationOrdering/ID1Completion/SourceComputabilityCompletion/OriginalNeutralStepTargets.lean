module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepInverseTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralStepTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open ClaudeSupervisedCompletion

/-- On the SAME final globally selectable tuple, an accepted original raw
neutral step is either literal same-type bottom or a recovered lifted
application step with an actually accepted child. The unpeeled branch is
discharged by the paid leaf law. Every state/child/constructor witness is
bound internally. This is raw inversion, not canonical quotient inversion. -/
def ActualOriginalNeutralStepElimination : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let r := OriginalVariableRepresentative.refineInputs (OriginalNeutralLeaf.refineInputs p)
  let data := OuterSelection.data r.base r.window
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (S T K parameter typeCode : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma (stepAccepted data r.oldStep S T K parameter)) →
  Nonempty (Derivation body Gamma
    (graph2 (BottomRepresentative.windowAt r.window) InternalOriginalStepGuard.one S parameter)) →
  Nonempty (Derivation body Gamma (graph1 OriginalNeutralLeaf.neutralTest InternalOriginalStepGuard.one S)) →
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralStepTargets
