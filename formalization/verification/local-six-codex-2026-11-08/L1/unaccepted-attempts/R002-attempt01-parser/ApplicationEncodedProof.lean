module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationEncodedProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data validity)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem sourceFromFold (data : Data) (out parent parameter : OTerm α)
    (hv : Nonempty (Derivation body Delta (graph2 (validity data) (suc z) parent parameter)))
    (hn : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph data out parent parameter))) :
    Nonempty (Derivation body Delta (graph2 (sourceRepresentative data) out parent parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons parent (Fin.cons parameter Fin.elim0)
  exact successorBranchIntro (InternalApplicationValidityStack.exactOne (validity data))
    (InternalAcceptance.constantZero 2) (InternalParameterizedCanonicalResultFold.foldN data)
    out z xs
    (sameAccept (validity data) (InternalLessThan.constantOne 2) (suc z) xs hv
      (InternalLessThanSupportProof.oneConstantValue xs)) hn

/-- Reconstruct the SAME quotient-edge checker at the two supplied J
outputs, with every raw witness obtained from the original constructors.
The argument and original lifted certificate never change representation. -/
theorem encodedLift (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (oldStep : Program 4) (sigma tau : Ty)
    (x y a certificate out other s t k sourceApp targetApp liftedStep lifted parameter gammaCode : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (Application.parameterPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (normalizeData base) oldStep sigma tau x y a certificate out other parameter gammaCode)))
    (hw : Nonempty (Derivation body Delta
      (Application.constructorWitnesses sigma tau a certificate s t k sourceApp targetApp liftedStep lifted))) :
    Nonempty (Derivation body Delta (edgeAccepted (normalizeData base) oldStep out other lifted parameter)) := by
  let data := normalizeData base
  let arrow : OTerm α := numeral (typeNumber (.arrow sigma tau))
  let d : OTerm α := numeral (typeNumber sigma)
  let e : OTerm α := numeral (typeNumber tau)
  have hconstructors := andLeft hw
  have hselectors := edgeSelectors certificate s t k (andLeft hconstructors)
  have hcore := andRight hp
  have hx := andLeft hcore
  have ha := andLeft (andRight hcore)
  have hedge := SupportProof.checkerRecover data oldStep x y certificate s t k parameter hselectors
    (andLeft (andRight (andRight hcore)))
  obtain ⟨hvs,hvt,htags⟩ := TypingProof.stepParts data oldStep s t k parameter (andLeft hedge)
  have hsTag := ApplicationRawProof.sourceRawTag data oldStep x y s t k arrow parameter hx hedge
  have htTag := TypingProof.targetTag s t k arrow parameter htags hsTag
  have harg := InternalOriginalUniformDescentSelectionInternalProof.typedRecover data.oldRepresentative
    (validity data) data.member a d parameter ha
  have hva := andLeft (andRight harg)
  have haTag := andLeft (andRight (andRight harg))
  have hf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover data.oldRepresentative
    (validity data) data.member x arrow parameter hx
  have hm := InternalOriginalUniformApplicationTypingMembershipProof.codomainMembership
    n arity base hc symbols S table hS sigma tau parameter gammaCode (andLeft hp) (andLeft hf)
  have har := InternalTypedEdgePresentationSupportProof.arrowNumeral (body := body) (Gamma := Delta) (α := α) sigma tau
  have hend := ApplicationRawProof.endpointFromCore n arity base hc symbols S table hS oldStep
    sigma tau x y a certificate out other s t k parameter gammaCode hp hedge
  have hsapp := andLeft (andRight hconstructors)
  have htapp := andLeft (andRight (andRight hconstructors))
  have hk := andRight (andRight (andRight hconstructors))
  have hstep := ApplicationStepProof.applicationStep data oldStep arrow d e s t a k
    sourceApp targetApp liftedStep parameter har hsTag htTag haTag hend hsapp htapp hk (andLeft hedge)
  have hns := TypingProof.sourceFold data x s parameter hvs (andLeft (andRight hedge))
  have hgraphs := andRight (andRight (andRight hcore))
  have hs := InternalParameterizedCanonicalResultFoldRepresentativeProof.representativeApplication data
    arrow d e s a sourceApp x out parameter
    (andIntro har (andIntro hvs (andIntro hsTag (andIntro hva (andIntro haTag
      (andIntro hm (andIntro hns (andIntro hsapp (andLeft hgraphs)))))))))
  have ht := InternalParameterizedCanonicalResultFoldRepresentativeProof.representativeApplication data
    arrow d e t a targetApp y other parameter
    (andIntro har (andIntro hvt (andIntro htTag (andIntro hva (andIntro haTag
      (andIntro hm (andIntro (andRight (andRight hedge)) (andIntro htapp (andRight hgraphs)))))))))
  have hsource := sourceFromFold data out sourceApp parameter (andLeft hs)
    (andRight (andLeft (andRight hs)))
  have htarget := andRight (andLeft (andRight ht))
  exact SupportProof.checkerAccept data oldStep out other lifted sourceApp targetApp liftedStep parameter
    (edgeSelectors lifted sourceApp targetApp liftedStep (andRight hw))
    (andIntro hstep (andIntro hsource htarget))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationEncodedProof
