module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixObjectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionFunctionalityProof
open InternalParameterizedPathChecker InternalParameterizedPathCheckerProof InternalParameterizedApplicationPathLiftSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalQuotientComparisonProof (orLeft orRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open UniformCertificateCompletion OriginalSameCodeSuffix
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Same raw payload and Gamma give equality of the original pair Objects. -/
theorem objectsEqual (source target gammaCode x y : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing source gammaCode x)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing target gammaCode y)))
    (he : Nonempty (Derivation body Gamma (equal x y))) :
    Nonempty (Derivation body Gamma (equal source target)) := by
  have hs' : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing source gammaCode y)) := by
    apply graphInputTransport body alpha 2 Gamma (OrdinaryArithmetic.graphFormula InternalPairing.pairing)
      source (Fin.cons gammaCode (Fin.cons x Fin.elim0))
      (Fin.cons gammaCode (Fin.cons y Fin.elim0)) _ hs
    intro i
    exact Fin.cases (UniformCertificateCompletion.PathSupportProof.equalReflexive gammaCode) (Fin.cases he (fun q => Fin.elim0 q)) i
  rw [equalEqn]
  exact valueUnique InternalPairing.pairing source target (Fin.cons gammaCode (Fin.cons y Fin.elim0)) hs' ht

theorem objectAt (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (window : Program 1)
    (hguards : PositivePathGuards data window oldStep) (context : Nat)
    (source target gammaCode x y code typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma
      (objectPremises data window oldStep context source target gammaCode x y code typ parameter))) :
    Nonempty (Derivation body Gamma
      (objectConclusion (Outer.source oldSrc oldComp data rawScalar oldStep
        BottomRepresentative.bottomTest BottomSpineMeasure.measure window) context source target code)) := by
  let P := equal code z
  have hw := andLeft hp
  have hparameter := andLeft (andRight hp)
  have hsource := andLeft (andRight (andRight hp))
  have htarget := andLeft (andRight (andRight (andRight hp)))
  have hxtype := andLeft (andRight (andRight (andRight (andRight hp))))
  have hytype := andLeft (andRight (andRight (andRight (andRight (andRight hp)))))
  have hpath := andRight (andRight (andRight (andRight (andRight (andRight hp)))))
  apply formulaCases P
  · have hecode : Nonempty (Derivation body (P :: Gamma) (eqn code z)) := by
      rw [← equalEqn]
      exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hnil := checkerCodeTransport (edgeChecker data oldStep) false x y code z parameter hecode (withHyp hpath P)
    have he := nilRecover (edgeChecker data oldStep) x y parameter hnil
    obtain ⟨ho⟩ := objectsEqual source target gammaCode x y (withHyp hsource P) (withHyp htarget P) he
    exact ⟨orLeft (Derivation.conjunctionIntroduction (Derivation.hypothesis List.mem_cons_self) ho)⟩
  · have hn : Nonempty (Derivation body (P.not :: Gamma) (equal code z).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hpositive := OriginalSameCodeSuffixNonzeroProof.nonzero (edgeChecker data oldStep)
      x y code parameter hn (withHyp hpath P.not)
    have hwindow := OuterWindowProof.parameterWindow window context x parameter gammaCode
      (withHyp hw P.not) (withHyp hparameter P.not)
    have hpre := andIntro hwindow
      (andIntro (withHyp hxtype P.not) (andIntro (withHyp hytype P.not) hpositive))
    obtain ⟨hg⟩ := hguards body alpha (P.not :: Gamma) x y code typ parameter
    obtain ⟨hpre⟩ := hpre
    have hraw : Nonempty (Derivation body (P.not :: Gamma)
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure
        (edgeChecker data oldStep) x y code parameter)) :=
      ⟨Derivation.implicationElimination hg hpre⟩
    have hs := withHyp hsource P.not
    have ht := withHyp htarget P.not
    obtain ⟨hcert⟩ := OuterPositiveProof.positiveAccept oldSrc oldComp data rawScalar oldStep
      BottomRepresentative.bottomTest BottomSpineMeasure.measure window context typ source target code
      gammaCode x y parameter (withHyp hw P.not)
      (pairLeft source gammaCode x hs) (pairLeft target gammaCode y ht)
      (pairRight source gammaCode x hs) (pairRight target gammaCode y ht)
      (withHyp hparameter P.not) (withHyp hxtype P.not) (withHyp hytype P.not) hraw
    exact ⟨orRight (Derivation.conjunctionIntroduction (Derivation.hypothesis List.mem_cons_self) hcert)⟩

/-- Generic arithmetic packaging only. The final exact alias supplies the
proved guards at the same final tuple, rather than assuming them there. -/
theorem objectSuffix (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (window : Program 1)
    (hguards : PositivePathGuards data window oldStep) (context : Nat) :
    ObjectSuffix data window oldStep
      (Outer.source oldSrc oldComp data rawScalar oldStep BottomRepresentative.bottomTest
        BottomSpineMeasure.measure window) context := by
  intro body alpha Gamma source target gammaCode x y code typ parameter
  let P := objectPremises data window oldStep context source target gammaCode x y code typ parameter
  obtain ⟨h⟩ := objectAt oldSrc oldComp data rawScalar oldStep window hguards context
    source target gammaCode x y code typ parameter
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixObjectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixObjectProof
