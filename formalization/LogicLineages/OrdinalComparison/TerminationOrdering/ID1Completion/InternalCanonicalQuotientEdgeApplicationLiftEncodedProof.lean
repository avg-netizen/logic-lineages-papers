module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftRepresentativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEncodedProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCanonicalQuotientEdgeApplicationLift
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalCanonicalQuotientEdgeApplicationLiftEndpointProof
open InternalCanonicalQuotientEdgeApplicationLiftRepresentativeProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The source representative selects the actual N branch using the derived
parent validity. No new source representative or semantic equality is used. -/
theorem sourceFromFold (data : Data) (out parent : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalDescentSelection.validity data).sourceValid
        InternalOriginalStepGuard.one parent)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalResultFoldCalibration.normalizer data) out parent))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalCanonicalQuotientEdgeSelection.edgeData data).sourceRepresentative out parent)) := by
  let V := (InternalCanonicalDescentSelection.validity data).sourceValid
  let xs : Fin 1 → OTerm α := Fin.cons parent Fin.elim0
  exact successorBranchIntro (InternalApplicationValidityStack.exactOne V)
    (InternalAcceptance.constantZero 1) (InternalCanonicalResultFoldCalibration.normalizer data)
    out z xs
    (InternalApplicationStepPeelSupportProof.sameAccept V
      (InternalLessThan.constantOne 1) (suc z) xs hv
      (InternalLessThanSupportProof.oneConstantValue xs)) hn

/-- Every raw endpoint, parent W and parent representative graph is derived
from the exact frozen core and original constructor witnesses. -/
theorem encodedLift (S : List Ty) (data : Data)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S data.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (x y a certificate out other s t k sourceApp targetApp liftedStep lifted : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (corePremises data sigma tau x y a certificate out other)))
    (hw : Nonempty (Derivation body Gamma
      (constructorWitnesses sigma tau a certificate s t k sourceApp targetApp liftedStep lifted))) :
    Nonempty (Derivation body Gamma (edgeAccepted data out other lifted)) := by
  let arrow : OTerm α := numeral (typeNumber (.arrow sigma tau))
  let d : OTerm α := numeral (typeNumber sigma)
  let e : OTerm α := numeral (typeNumber tau)
  have hconstructors := andLeft hw
  have hselectors := edgeSelectors certificate s t k (andLeft hconstructors)
  have hedge := InternalQuotientEdgeCheckerSupportProof.checkerRecover
    (InternalCanonicalQuotientEdgeSelection.edgeData data) x y certificate s t k hselectors
    (andLeft (andRight (andRight hp)))
  have hep := endpointFromCore S data hm hc sigma tau x y a certificate out other
    s t k hp hselectors
  have har := andLeft hep
  have hend := andLeft (andRight hep)
  have hraw := andLeft (andRight (andRight hep))
  have hvt := andRight (andRight (andRight hep))
  have hvs := andLeft hraw
  have hva := andLeft (andRight (andRight hraw))
  have htags := andLeft (andRight (andRight (andRight hraw)))
  have hmember := andRight (andRight (andRight (andRight hraw)))
  have hsapp := andLeft (andRight hconstructors)
  have htapp := andLeft (andRight (andRight hconstructors))
  have hklift := andRight (andRight (andRight hconstructors))
  have hstep := InternalCanonicalQuotientEdgeSelectionSupportProof.applicationStep data
    arrow d e s t a k sourceApp targetApp liftedStep
    (andIntro (andIntro har (andIntro hend (andIntro hsapp htapp))) hklift) (andLeft hedge)
  have hns := InternalCanonicalQuotientEdgeSelectionTypingProof.sourceFold data x s hvs
    (andLeft (andRight hedge))
  have hcombine := andRight (andRight (andRight hp))
  have hs := representativeApplication data arrow d e s a sourceApp x out
    (andIntro har (andIntro hvs (andIntro (andLeft htags)
      (andIntro hva (andIntro (andRight (andRight htags))
        (andIntro hmember (andIntro hns (andIntro hsapp (andLeft hcombine)))))))))
  have ht := representativeApplication data arrow d e t a targetApp y other
    (andIntro har (andIntro hvt (andIntro (andLeft (andRight htags))
      (andIntro hva (andIntro (andRight (andRight htags))
        (andIntro hmember (andIntro (andRight (andRight hedge))
          (andIntro htapp (andRight hcombine)))))))))
  have hsource := sourceFromFold data out sourceApp (andLeft hs)
    (andRight (andLeft (andRight hs)))
  have htarget := andRight (andLeft (andRight ht))
  exact InternalQuotientEdgeCheckerSupportProof.checkerAccept
    (InternalCanonicalQuotientEdgeSelection.edgeData data) out other lifted sourceApp targetApp liftedStep
    (edgeSelectors lifted sourceApp targetApp liftedStep (andRight hw))
    (andIntro hstep (andIntro hsource htarget))

theorem actualOriginalCanonicalEncodedQuotientEdgeApplicationLift :
    InternalCanonicalQuotientEdgeApplicationLiftTargets.ActualOriginalCanonicalEncodedQuotientEdgeApplicationLift := by
  intro S data hm hc body sigma tau α Delta x y a certificate out other s t k sourceApp targetApp liftedStep lifted
  let premise := corePremises data sigma tau x y a certificate out other ⊓
    constructorWitnesses sigma tau a certificate s t k sourceApp targetApp liftedStep lifted
  have h : Nonempty (Derivation body (premise :: Delta) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := encodedLift S data hm hc sigma tau x y a certificate out other
    s t k sourceApp targetApp liftedStep lifted (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEncodedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEncodedProof
