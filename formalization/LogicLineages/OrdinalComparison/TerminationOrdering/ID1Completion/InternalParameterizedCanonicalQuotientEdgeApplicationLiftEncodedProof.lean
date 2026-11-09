module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerNormalizedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldRepresentativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEncodedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalParameterizedCanonicalQuotientEdgeApplicationLift
open InternalParameterizedCanonicalQuotientEdgeApplicationLiftEndpointProof
open InternalParameterizedCanonicalQuotientEdgeApplicationLiftTypedProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Original selector witnesses expose W and both actual N graphs. Their
lifted W and representatives are then derived for the same raw applications.
The final checker retains both canonical typed guards. -/
theorem encodedLift (data : Data) (oldStep : Program 4)
    (arrow d e x y a certificate out other s t k sourceApp targetApp liftedStep lifted parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (corePremises data oldStep arrow d e x y a certificate out other parameter)))
    (hw : Nonempty (Derivation body Gamma
      (constructorWitnesses d e a certificate s t k sourceApp targetApp liftedStep lifted))) :
    Nonempty (Derivation body Gamma (edgeAccepted data oldStep out other lifted parameter)) := by
  have har := andLeft (andLeft hp)
  have hm := andRight (andLeft hp)
  have hi := andRight hp
  have hx := andLeft hi
  have ha := andLeft (andRight hi)
  have he := andLeft (andRight (andRight hi))
  have hj := andRight (andRight (andRight hi))
  have hconstructors := andLeft hw
  have hselectors := edgeSelectors certificate s t k (andLeft hconstructors)
  have hraw := InternalParameterizedQuotientEdgeCheckerNormalizedProof.normalizedRecover
    data oldStep x y certificate s t k parameter hselectors
    (InternalParameterizedQuotientEdgeCheckerTypedProof.acceptedCore
      data oldStep x y certificate parameter he)
  have hstep := andLeft hraw
  have hns := andLeft (andRight hraw)
  have hnt := andRight (andRight hraw)
  have hvs := InternalOriginalUniformStepGuardSupportProof.stepSourceValidity
    data oldStep s t k parameter hstep
  have hls := rawSourceTag data x s arrow parameter hx hvs hns
  have hg := InternalOriginalUniformStepGuardSupportProof.taggedStepRecover
    data oldStep arrow s t k parameter hls hstep
  have hvt := andLeft (andRight hg)
  have htt := andLeft (andRight (andRight hg))
  have hlt := andLeft (andRight (andRight (andRight hg)))
  have haf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (validity data) data.member a d parameter ha
  have hva := andLeft (andRight haf)
  have hla := andLeft (andRight (andRight haf))
  have hend := InternalParameterizedStructuralEndpointGuardSupportProof.endpointAccept
    (validity data) (targetValidity data) data.member arrow d e s t a parameter har
    (andIntro hvs (andIntro htt (andIntro hva
      (andIntro (andIntro hls (andIntro hlt hla)) hm))))
  have hsapp := andLeft (andRight hconstructors)
  have htapp := andLeft (andRight (andRight hconstructors))
  have hklift := andRight (andRight (andRight hconstructors))
  have hlift := InternalOriginalUniformStepGuardApplicationProof.applicationStep
    data oldStep arrow d e s t a k sourceApp targetApp liftedStep parameter
    (andIntro (andIntro har (andIntro hend (andIntro hsapp htapp))) hklift) hstep
  have hs := InternalParameterizedCanonicalResultFoldRepresentativeProof.representativeApplication
    data arrow d e s a sourceApp x out parameter
    (andIntro har (andIntro hvs (andIntro hls (andIntro hva (andIntro hla
      (andIntro hm (andIntro hns (andIntro hsapp (andLeft hj)))))))))
  have ht := InternalParameterizedCanonicalResultFoldRepresentativeProof.representativeApplication
    data arrow d e t a targetApp y other parameter
    (andIntro har (andIntro hvt (andIntro hlt (andIntro hva (andIntro hla
      (andIntro hm (andIntro hnt (andIntro htapp (andRight hj)))))))))
  have hcore := InternalParameterizedQuotientEdgeCheckerNormalizedProof.normalizedAcceptEncoded
    data oldStep out other lifted sourceApp targetApp liftedStep parameter (andRight hw)
    (andIntro hlift (andIntro (andRight (andLeft (andRight hs)))
      (andRight (andLeft (andRight ht)))))
  have htyped := applicationTypedOutputs data oldStep arrow d e x y a certificate out other parameter hp
  exact InternalParameterizedQuotientEdgeCheckerTypedProof.wrapperAccept
    data oldStep out other lifted e parameter
    (InternalParameterizedQuotientEdgeCheckerTypedProof.typedSourceTag
      data out e parameter (andLeft htyped)) (andIntro hcore htyped)

theorem actualParameterizedEncodedCanonicalQuotientEdgeApplicationLift :
    InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets.ActualParameterizedEncodedCanonicalQuotientEdgeApplicationLift := by
  intro body data oldStep α Delta arrow d e x y a certificate out other s t k sourceApp targetApp liftedStep lifted parameter
  let P := corePremises data oldStep arrow d e x y a certificate out other parameter ⊓
    constructorWitnesses d e a certificate s t k sourceApp targetApp liftedStep lifted
  have h : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hresult⟩ := encodedLift data oldStep arrow d e x y a certificate out other
    s t k sourceApp targetApp liftedStep lifted parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hresult⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEncodedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEncodedProof
