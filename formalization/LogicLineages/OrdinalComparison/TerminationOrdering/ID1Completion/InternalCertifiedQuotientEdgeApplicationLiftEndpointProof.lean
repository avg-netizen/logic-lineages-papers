module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftEndpointProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCertifiedQuotientEdgeApplicationLift
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Repackage the SAME finite leaves for the checked endpoint presentation.
Only its base step is used; neither a new representative nor a new selection
is chosen. Its representatives agree definitionally with the selected ones. -/
def presentationData (data : Data) : InternalTypedEdgePresentation.Data where
  validity := InternalCertifiedSourceGuardSelection.validity data
  member := data.member
  oldEdge := InternalRepresentativeFoldCalibration.foldedData
    data.oldValidity data.member data.oldEdge
  oldTyped := data.oldTyped

theorem endpointFromCore (S : List Ty) (data : Data)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S data.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (x y a certificate out other s t k : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (corePremises data sigma tau x y a certificate out other)))
    (hselectors : Nonempty (Derivation body Gamma (selectors certificate s t k))) :
    Nonempty (Derivation body Gamma
      (InternalTypedEdgePresentation.requirements (presentationData data) sigma tau s t a)) := by
  have hx := InternalCertifiedSourceGuardSelectionSupportProof.typedRecover data x
    (numeral (typeNumber (.arrow sigma tau))) (andLeft hp)
  have ha := InternalCertifiedSourceGuardSelectionSupportProof.typedRecover data a
    (numeral (typeNumber sigma)) (andLeft (andRight hp))
  have hedge := InternalQuotientEdgeCheckerSupportProof.checkerRecover
    (InternalCertifiedSourceGuardSelection.edgeData data) x y certificate s t k
    hselectors (andLeft (andRight (andRight hp)))
  have hstep := InternalCertifiedSourceGuardSelectionSupportProof.stepRecover data s t k (andLeft hedge)
  have hbase := InternalQuotientEdgeCheckerSupportProof.checkerAccept
    (InternalTypedEdgePresentation.edgeData (presentationData data)) x y certificate s t k
    hselectors (andIntro (andLeft hstep) (andRight hedge))
  exact InternalTypedEdgePresentationSupportProof.presentation S (presentationData data) hm hc
    sigma tau x y a certificate s t k
    (andIntro (andLeft hx) (andIntro (andLeft ha) (andIntro hselectors hbase)))

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftEndpointProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftEndpointProof
