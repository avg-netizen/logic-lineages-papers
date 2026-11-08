module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCertifiedSourceGuardSelection
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalCertifiedSourceGuardSelectionSupportProof
open InternalRepresentativeApplicationCongruenceSupportProof (oneRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem goodAtCombine (data : Data)
    (arrow d e f a parent fp ap nf na out : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph1 (validity data).sourceValid InternalOriginalStepGuard.one parent)))
    (hf : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one a)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hap : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hnf : Nonempty (Derivation body Gamma (graph1 (normalizer data) nf f)))
    (hna : Nonempty (Derivation body Gamma (graph1 (normalizer data) na a)))
    (hout : Nonempty (Derivation body Gamma (graph4 (InternalRepresentativeFoldCalibration.combine data.oldEdge) out d e nf na)))
    : Nonempty (Derivation body Gamma
      (graph1 (goodRun data) InternalOriginalStepGuard.one parent)) := by
  exact andLeft (InternalApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
    (InternalRepresentativeFoldCalibration.rootGuard data.oldValidity data.member)
    (InternalRepresentativeFoldCalibration.leaf data.oldValidity data.member data.oldEdge)
    (InternalRepresentativeFoldCalibration.combine data.oldEdge)
    arrow d e fp ap f a parent nf na out har
    (reconstructPair f arrow fp hfl hfp) (reconstructPair a d ap hal hap)
    (applicationForward d e f a fp ap parent hfp hap hp) hv
    (andIntro hf hnf) (andIntro ha hna) hout)

theorem goodAtOutputs (data : Data)
    (arrow d e f a parent fp ap nf na : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph1 (validity data).sourceValid InternalOriginalStepGuard.one parent)))
    (hf : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one a)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hap : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hnf : Nonempty (Derivation body Gamma (graph1 (normalizer data) nf f)))
    (hna : Nonempty (Derivation body Gamma (graph1 (normalizer data) na a)))
    : Nonempty (Derivation body Gamma
      (graph1 (goodRun data) InternalOriginalStepGuard.one parent)) := by
  apply programCases (InternalRepresentativeFoldCalibration.combine data.oldEdge) (Fin.cons d (Fin.cons e (Fin.cons nf (Fin.cons na Fin.elim0)))) _
  intro β j Delta out hj hout
  simp only [graph1Rename, oneRename]
  simp only [consTermRename, emptyRename] at hout
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hp' := renameInto hp j Delta hj
  have hv' := renameInto hv j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hfp' := renameInto hfp j Delta hj
  have hap' := renameInto hap j Delta hj
  have hnf' := renameInto hnf j Delta hj
  have hna' := renameInto hna j Delta hj
  simp only [graph1Rename, graph2Rename, graph4Rename, oneRename] at har' hfl' hal' hp' hv' hf' ha' hfp' hap' hnf' hna'
  exact goodAtCombine data (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j) (parent.relabel j) (fp.relabel j) (ap.relabel j) (nf.relabel j) (na.relabel j) out
    har' hfl' hal' hp' hv' hf' ha' hfp' hap' hnf' hna' hout

theorem goodAtFunctionOutput (data : Data)
    (arrow d e f a parent fp ap nf : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph1 (validity data).sourceValid InternalOriginalStepGuard.one parent)))
    (hf : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one a)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hap : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hnf : Nonempty (Derivation body Gamma (graph1 (normalizer data) nf f)))
    : Nonempty (Derivation body Gamma
      (graph1 (goodRun data) InternalOriginalStepGuard.one parent)) := by
  apply programCases (normalizer data) (Fin.cons a Fin.elim0) _
  intro β j Delta na hj hna
  simp only [graph1Rename, oneRename]
  simp only [consTermRename, emptyRename] at hna
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hp' := renameInto hp j Delta hj
  have hv' := renameInto hv j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hfp' := renameInto hfp j Delta hj
  have hap' := renameInto hap j Delta hj
  have hnf' := renameInto hnf j Delta hj
  simp only [graph1Rename, graph2Rename, graph4Rename, oneRename] at har' hfl' hal' hp' hv' hf' ha' hfp' hap' hnf'
  exact goodAtOutputs data (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j) (parent.relabel j) (fp.relabel j) (ap.relabel j) (nf.relabel j) na
    har' hfl' hal' hp' hv' hf' ha' hfp' hap' hnf' hna

theorem goodAtPayloads (data : Data)
    (arrow d e f a parent fp ap : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph1 (validity data).sourceValid InternalOriginalStepGuard.one parent)))
    (hf : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one a)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hap : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    : Nonempty (Derivation body Gamma
      (graph1 (goodRun data) InternalOriginalStepGuard.one parent)) := by
  apply programCases (normalizer data) (Fin.cons f Fin.elim0) _
  intro β j Delta nf hj hnf
  simp only [graph1Rename, oneRename]
  simp only [consTermRename, emptyRename] at hnf
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hp' := renameInto hp j Delta hj
  have hv' := renameInto hv j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hfp' := renameInto hfp j Delta hj
  have hap' := renameInto hap j Delta hj
  simp only [graph1Rename, graph2Rename, graph4Rename, oneRename] at har' hfl' hal' hp' hv' hf' ha' hfp' hap'
  exact goodAtFunctionOutput data (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j) (parent.relabel j) (fp.relabel j) (ap.relabel j) nf
    har' hfl' hal' hp' hv' hf' ha' hfp' hap' hnf

theorem goodAtFunctionPayload (data : Data)
    (arrow d e f a parent fp : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph1 (validity data).sourceValid InternalOriginalStepGuard.one parent)))
    (hf : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one a)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    : Nonempty (Derivation body Gamma
      (graph1 (goodRun data) InternalOriginalStepGuard.one parent)) := by
  apply programCases InternalUnpair.right (Fin.cons a Fin.elim0) _
  intro β j Delta ap hj hap
  simp only [graph1Rename, oneRename]
  simp only [consTermRename, emptyRename] at hap
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hp' := renameInto hp j Delta hj
  have hv' := renameInto hv j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hfp' := renameInto hfp j Delta hj
  simp only [graph1Rename, graph2Rename, graph4Rename, oneRename] at har' hfl' hal' hp' hv' hf' ha' hfp'
  exact goodAtPayloads data (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j) (parent.relabel j) (fp.relabel j) ap
    har' hfl' hal' hp' hv' hf' ha' hfp' hap

theorem parentGoodRun (data : Data)
    (arrow d e f a parent : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph1 (validity data).sourceValid InternalOriginalStepGuard.one parent)))
    (hf : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one f)))
    (ha : Nonempty (Derivation body Gamma (graph1 (goodRun data) InternalOriginalStepGuard.one a)))
    : Nonempty (Derivation body Gamma
      (graph1 (goodRun data) InternalOriginalStepGuard.one parent)) := by
  apply programCases InternalUnpair.right (Fin.cons f Fin.elim0) _
  intro β j Delta fp hj hfp
  simp only [graph1Rename, oneRename]
  simp only [consTermRename, emptyRename] at hfp
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hp' := renameInto hp j Delta hj
  have hv' := renameInto hv j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  simp only [graph1Rename, graph2Rename, graph4Rename, oneRename] at har' hfl' hal' hp' hv' hf' ha'
  exact goodAtFunctionPayload data (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j) (parent.relabel j) fp
    har' hfl' hal' hp' hv' hf' ha' hfp

/-- Both application roots are source-valid. The second is obtained by
rebuilding the same structural endpoint at (t,t,a). -/
theorem parentSourceValidities (data : Data)
    (arrow d e s t a sourceApp targetApp : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (InternalApplicationValidityClosure.endpointApplicationPremises
        data.oldValidity data.member arrow d e s t a sourceApp targetApp)))
    (ht : Nonempty (Derivation body Gamma
      (graph1 (validity data).sourceValid InternalOriginalStepGuard.one t))) :
    Nonempty (Derivation body Gamma
      (graph1 (validity data).sourceValid InternalOriginalStepGuard.one sourceApp ⊓
        graph1 (validity data).sourceValid InternalOriginalStepGuard.one targetApp)) := by
  have har := andLeft hp
  have hr := InternalStructuralEndpointGuardSupportProof.endpointRecover
    (validity data) data.member arrow d e s t a har (andLeft (andRight hp))
  have ha := andLeft (andRight (andRight hr))
  have htail := andRight (andRight (andRight hr))
  have htags := andLeft htail
  have htl := andLeft (andRight htags)
  have hal := andRight (andRight htags)
  have hm := andRight htail
  have htapp := andRight (andRight (andRight hp))
  have he := InternalStructuralEndpointGuardSupportProof.endpointAccept
    (validity data) data.member arrow d e t t a har
    (andIntro ht (andIntro (andLeft (andRight hr))
      (andIntro ha (andIntro (andIntro htl (andIntro htl hal)) hm))))
  have hv := InternalApplicationValidityClosureEndpointProof.endpointApplicationValidity
    data.oldValidity data.member arrow d e s t a sourceApp targetApp hp
  have hvt := InternalApplicationValidityClosureEndpointProof.endpointApplicationValidity
    data.oldValidity data.member arrow d e t t a targetApp targetApp
    (andIntro har (andIntro he (andIntro htapp htapp)))
  exact andIntro (andLeft hv) (andLeft hvt)

/-- Arbitrary internal contexts; no argument fixed-point or external
calibration is used to establish either successful parent run. -/
theorem stepClosure (data : Data)
    (arrow d e s t a k sourceApp targetApp liftedStep : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (InternalCertifiedQuotientEdgeApplicationLift.stepLiftPremises data
        arrow d e s t a k sourceApp targetApp liftedStep))) :
    Nonempty (Derivation body Gamma (stepAccepted data sourceApp targetApp liftedStep)) := by
  have hp := andLeft h
  have hs := stepRecover data s t k (andLeft (andRight h))
  have harg := andRight (andRight h)
  have hb := InternalOriginalApplicationStepSupportProof.applicationStep (baseData data)
    arrow d e s t a k sourceApp targetApp liftedStep hp (andLeft hs)
  have he := andLeft hp
  have hv := parentSourceValidities data arrow d e s t a sourceApp targetApp he
    (andLeft (andRight hs))
  have har := andLeft he
  have hr := InternalStructuralEndpointGuardSupportProof.endpointRecover
    (validity data) data.member arrow d e s t a har (andLeft (andRight he))
  have htags := andLeft (andRight (andRight (andRight hr)))
  have hgood := andRight (andRight hs)
  have hgs := parentGoodRun data arrow d e s a sourceApp har
    (andLeft htags) (andRight (andRight htags))
    (andLeft (andRight (andRight he))) (andLeft hv) (andLeft hgood) harg
  have hgt := parentGoodRun data arrow d e t a targetApp har
    (andLeft (andRight htags)) (andRight (andRight htags))
    (andRight (andRight (andRight he))) (andRight hv) (andRight hgood) harg
  exact stepAccept data sourceApp targetApp liftedStep
    (andIntro hb (andIntro (andRight hv) (andIntro hgs hgt)))

theorem actualOriginalCertifiedApplicationStepClosure :
    InternalCertifiedQuotientEdgeApplicationLiftTargets.ActualOriginalCertifiedApplicationStepClosure := by
  intro data body α arrow d e s t a k sourceApp targetApp liftedStep
  let premise := InternalCertifiedQuotientEdgeApplicationLift.stepLiftPremises data
    arrow d e s t a k sourceApp targetApp liftedStep
  have hp : Nonempty (Derivation body [premise] premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := stepClosure data arrow d e s t a k sourceApp targetApp liftedStep hp
  exact ⟨Derivation.implicationIntroduction h⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftStepProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftStepProof
