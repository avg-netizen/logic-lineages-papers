module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalConstructorLeaf InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Dual orientation of equality recovery: the supplied left output determines
the right output. Its existential witness is discharged by Program totality. -/
theorem sameKnownLeftRecover {n : Nat} (p q : Program n) (value : OTerm α)
    (xs : Fin n → OTerm α)
    (hs : Nonempty (Derivation body Delta
      (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
    (hp : Nonempty (Derivation body Delta (programGraph p value xs))) :
    Nonempty (Derivation body Delta (programGraph q value xs)) := by
  apply programCases q xs _
  intro β j Theta actual hj hq
  simp only [programRename]
  have hs' := renameInto hs j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [programRename,sucRelabel,zRelabel] at hs' hp'
  obtain ⟨he⟩ := InternalEqualityTestProof.equalityOfAcceptance (value.relabel j) actual
    (binaryRecover InternalEqualityTest.equalityTest p q (suc z) (value.relabel j) actual
      (fun i => (xs i).relabel j) hs' hp' hq)
  exact outputTransport q actual (value.relabel j) (fun i => (xs i).relabel j)
    ⟨InternalTagArithmeticSupportProof.symm he⟩ hq

theorem originalFactor (oldStep : Program 4) : OriginalFactor oldStep (refined oldStep) := by
  intro body α Delta rawSource target certificate parameter
  let P := accepted (refined oldStep) rawSource target certificate parameter
  let xs : Fin 4 → OTerm α := Fin.cons rawSource
    (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := andLeft (conjunctionRecover oldStep
    (InternalAcceptance.conjunction
      (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) variableGuard) xs hp)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Every step is an internal graph consequence at the supplied symbolic
terms. No numerical calibration or native source-case fact is imported. -/
theorem variableBottom (oldStep : Program 4) (rawSource target certificate parameter typeCode : OTerm α)
    (ha : Nonempty (Derivation body Delta
      (accepted (refined oldStep) rawSource target certificate parameter)))
    (hv : Nonempty (Derivation body Delta (graph1 variableTest (suc z) rawSource)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typeCode rawSource))) :
    Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode target typeCode)) := by
  let xs : Fin 4 → OTerm α := Fin.cons rawSource
    (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have guards := conjunctionRecover
    (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) variableGuard xs
    (andRight (conjunctionRecover oldStep
      (InternalAcceptance.conjunction
        (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) variableGuard) xs ha))
  have hvAt : Nonempty (Derivation body Delta (programGraph variableAt (suc z) xs)) :=
    unaryValue variableTest (.projection 0) (suc z) rawSource xs hv (projectionValue 0 xs)
  have hs := successorBranchElim
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize variableAt)
    (InternalLessThan.constantOne 4) (InternalApplicationStepPeel.same (.projection 1) expectedBottom)
    (suc z) z xs (normalizeAccept variableAt xs hvAt) (andRight guards)
  have hb := sameKnownLeftRecover (.projection 1) expectedBottom target xs hs (projectionValue 1 xs)
  have htAt : Nonempty (Derivation body Delta
      (programGraph (leftOf (.projection 0)) typeCode xs)) :=
    unaryValue InternalUnpair.left (.projection 0) typeCode rawSource xs ht (projectionValue 0 xs)
  exact unaryRecover BottomRepresentative.bottomCode (leftOf (.projection 0)) target typeCode xs hb htAt

theorem bottomReject (oldStep : Program 4) (rawSource target certificate parameter : OTerm α)
    (hb : Nonempty (Derivation body Delta
      (graph1 BottomRepresentative.bottomTest (suc z) rawSource))) :
    Nonempty (Derivation body Delta
      (accepted (refined oldStep) rawSource target certificate parameter).not) := by
  let P := accepted (refined oldStep) rawSource target certificate parameter
  let xs : Fin 4 → OTerm α := Fin.cons rawSource
    (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have guards := conjunctionRecover
    (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) variableGuard xs
    (andRight (conjunctionRecover oldStep
      (InternalAcceptance.conjunction
        (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) variableGuard) xs hp))
  obtain ⟨hn⟩ := PositiveSpineRulesSupportProof.nonBottomRecover
    BottomRepresentative.bottomTest xs (andLeft guards)
  obtain ⟨hb'⟩ := withHyp hb P
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hb')⟩

theorem constructorCases (oldStep : Program 4) : ConstructorCases (refined oldStep) := by
  intro body α Delta rawSource target certificate parameter typeCode
  constructor
  · let P := accepted (refined oldStep) rawSource target certificate parameter ⊓
      (graph1 variableTest InternalOriginalStepGuard.one rawSource ⊓
        graph1 InternalUnpair.left typeCode rawSource)
    have hp : Nonempty (Derivation body (P :: Delta) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := variableBottom oldStep rawSource target certificate parameter typeCode
      (andLeft hp) (andLeft (andRight hp)) (andRight (andRight hp))
    exact ⟨Derivation.implicationIntroduction h⟩
  · let P := graph1 BottomRepresentative.bottomTest InternalOriginalStepGuard.one rawSource
    obtain ⟨h⟩ := bottomReject oldStep rawSource target certificate parameter
      (show Nonempty (Derivation body (P :: Delta) P) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalConstructorLeafInternalCases :
    OriginalConstructorLeafTargets.ActualOriginalConstructorLeafInternalCases := by
  intro oldStep
  exact ⟨originalFactor oldStep,constructorCases oldStep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
