module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftEndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftRepresentativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftEncodedProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCertifiedQuotientEdgeApplicationLift
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalCertifiedQuotientEdgeApplicationLiftStepProof InternalCertifiedQuotientEdgeApplicationLiftEndpointProof
open InternalCertifiedQuotientEdgeApplicationLiftRepresentativeProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The endpoint, selected parent step and both representative graphs are
derived in the original calculus from the frozen core premises. -/
theorem encodedLift (S : List Ty) (data : Data)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S data.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (x y a certificate out other s t k sourceApp targetApp liftedStep lifted : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (corePremises data sigma tau x y a certificate out other)))
    (hw : Nonempty (Derivation body Gamma
      (constructorWitnesses sigma tau a certificate s t k sourceApp targetApp liftedStep lifted))) :
    Nonempty (Derivation body Gamma (coreAccepted data out other lifted)) := by
  let arrow : OTerm α := numeral (typeNumber (.arrow sigma tau))
  let d : OTerm α := numeral (typeNumber sigma)
  let e : OTerm α := numeral (typeNumber tau)
  have hconstructors := andLeft hw
  have hselectors := edgeSelectors certificate s t k (andLeft hconstructors)
  have hedge := InternalQuotientEdgeCheckerSupportProof.checkerRecover
    (InternalCertifiedSourceGuardSelection.edgeData data) x y certificate s t k hselectors
    (andLeft (andRight (andRight hp)))
  have hs := InternalCertifiedSourceGuardSelectionSupportProof.stepRecover data s t k (andLeft hedge)
  have ha := InternalCertifiedSourceGuardSelectionSupportProof.typedRecover data a d
    (andLeft (andRight hp))
  have hendpoint := endpointFromCore S data hm hc sigma tau x y a certificate out other s t k hp hselectors
  have har := andLeft hendpoint
  have hend := andLeft (andRight hendpoint)
  have htags := andRight (andRight hendpoint)
  have hsapp := andLeft (andRight hconstructors)
  have htapp := andLeft (andRight (andRight hconstructors))
  have hklift := andRight (andRight (andRight hconstructors))
  have he : Nonempty (Derivation body Gamma
      (InternalApplicationValidityClosure.endpointApplicationPremises
        data.oldValidity data.member arrow d e s t a sourceApp targetApp)) :=
    andIntro har (andIntro hend (andIntro hsapp htapp))
  have hpvalid := parentSourceValidities data arrow d e s t a sourceApp targetApp he
    (andLeft (andRight hs))
  have hstep := stepClosure data arrow d e s t a k sourceApp targetApp liftedStep
    (andIntro (andIntro he hklift)
      (andIntro (andLeft hedge) (andLeft (andRight ha))))
  have hraw := InternalStructuralEndpointGuardSupportProof.endpointRecover
    (InternalCertifiedSourceGuardSelection.validity data) data.member arrow d e s t a har hend
  have hcombine := andRight (andRight (andRight hp))
  have hsource := rawRepresentativeApplication true data arrow d e s a sourceApp x out
    har (andLeft htags) (andRight (andRight htags))
    (andLeft hraw) (andLeft hpvalid) (andLeft (andRight (andRight hs)))
    (andLeft (andRight ha)) (andRight (andRight ha)) hsapp (andLeft hcombine)
    (andLeft (andRight hedge))
  have htarget := rawRepresentativeApplication false data arrow d e t a targetApp y other
    har (andLeft (andRight htags)) (andRight (andRight htags))
    (andLeft (andRight hs)) (andRight hpvalid) (andRight (andRight (andRight hs)))
    (andLeft (andRight ha)) (andRight (andRight ha)) htapp (andRight hcombine)
    (andRight (andRight hedge))
  exact InternalQuotientEdgeCheckerSupportProof.checkerAccept
    (InternalCertifiedSourceGuardSelection.edgeData data) out other lifted sourceApp targetApp liftedStep
    (edgeSelectors lifted sourceApp targetApp liftedStep (andRight hw))
    (andIntro hstep (andIntro hsource htarget))

theorem actualOriginalCertifiedEncodedQuotientEdgeApplicationLift :
    InternalCertifiedQuotientEdgeApplicationLiftTargets.ActualOriginalCertifiedEncodedQuotientEdgeApplicationLift := by
  intro S data hm hc body sigma tau α x y a certificate out other s t k sourceApp targetApp liftedStep lifted
  let premise := corePremises data sigma tau x y a certificate out other ⊓
    constructorWitnesses sigma tau a certificate s t k sourceApp targetApp liftedStep lifted
  have h : Nonempty (Derivation body [premise] premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := encodedLift S data hm hc sigma tau x y a certificate out other
    s t k sourceApp targetApp liftedStep lifted (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction result⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftEncodedProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftEncodedProof
