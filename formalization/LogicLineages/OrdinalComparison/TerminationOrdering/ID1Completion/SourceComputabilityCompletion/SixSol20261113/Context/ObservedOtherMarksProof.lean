module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMarksProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem iffCommon (A B C : Formula alpha)
 (hab : Nonempty (Derivation body Delta (A.iff B)))
 (hac : Nonempty (Derivation body Delta (A.iff C))) :
 Nonempty (Derivation body Delta (B.iff C)) := by
 have hb : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hc : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hf⟩ := iffForward (withHyp hac B) (iffBackward (withHyp hab B) hb)
 obtain ⟨hr⟩ := iffForward (withHyp hab C) (iffBackward (withHyp hac C) hc)
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hr)⟩
theorem observationsCommon (common left right mark : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations common left mark)))
 (hr : Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations common right mark))) :
 Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations left right mark)) :=
 andIntro (iffCommon _ _ _ (andLeft hl) (andLeft hr))
 (andIntro (iffCommon _ _ _ (andLeft (andRight hl)) (andLeft (andRight hr)))
 (andIntro (iffCommon _ _ _ (andLeft (andRight (andRight hl))) (andLeft (andRight (andRight hr))))
 (andIntro (iffCommon _ _ _ (andLeft (andRight (andRight (andRight hl)))) (andLeft (andRight (andRight (andRight hr)))))
 (iffCommon _ _ _ (andRight (andRight (andRight (andRight hl)))) (andRight (andRight (andRight (andRight hr))))))))
/-- All five actual guard observations follow from the literal accepted relation
at the structural preminimum, not from native calibration or assumed guards. -/
theorem acceptedMarks (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (left right parameter mark : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W left parameter)))
 (ha : Nonempty (Derivation body Delta (OriginalAllPositionMinimumCoherenceTargets.Accepted
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P left right parameter))) :
 Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations left right mark)) := by
 let q := OriginalStructuralClassKeyDefinitions.inputs p H G W
 let K := OriginalStructuralClassKeyDefinitions.key p H G W
 have hr := OriginalAllPositionAcceptedProof.actualHitDomain q H G W P body alpha Delta left right parameter hd ha
 have hm := OriginalActiveClassKernelBranchProof.matrixFromRelation q H G W
   OriginalRawSyntaxTransport.variableRankPackedRaw P left right parameter hd
   (andLeft (OriginalAllPositionAcceptedProof.acceptedRecover q H G W P left right parameter hd ha))
 have hk := andLeft (andRight hm)
 apply programCases K (Fin.cons left (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta value hj hg
 have hd' := renameInto hd j Theta hj
 have hr' := renameInto hr j Theta hj
 have hk' := renameInto hk j Theta hj
 rw [OriginalActiveKernelMinimumSupportProof.domainRename] at hd' hr'
 rw [OriginalActiveClassKernelEqualityProof.keyGraphRename] at hk'
 simp only [consTermRename,emptyRename] at hg
 have ho := OriginalActiveClassKernelEqualityProof.keyTransfer K (left.relabel j) (right.relabel j)
   (parameter.relabel j) value hk' hg
 rw [OriginalLambdaTraversalObserverSyntaxProof.observationsRename]
 exact observationsCommon value (left.relabel j) (right.relabel j) (mark.relabel j)
   (ObservedOtherDomainProof.keyObservations p H G W _ _ _ _ hd' hg)
   (ObservedOtherDomainProof.keyObservations p H G W _ _ _ _ hr' ho)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMarksProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMarksProof
