module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRetentionProof
open UniformCertificateCompletion
open OriginalRankGuardedRepresentativeGlobalProof OriginalRankGuardedRepresentativeNativeProof
open OriginalTransparentMinimumNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut

theorem actualRetention : EvaluatorKeyPutTargets.ActualRetention := by
 intro n arity p H G W P hp hH hG hW hP
 let q := prepared p H G W
 let Q := classTest p H G W P
 let s := minimumInputs p H G W P
 have hprepared := SixSol20261113.Erasure.PutPreparationProof.actualPutPreparation n arity p H G W P hp hH hG hW hP
 have hq : GlobalSourcePackage.InputsCalibrated n arity q := hprepared.1
 have hQ := EvaluatorKeyCalibrationProof.calibrated n arity p H G W P hp hH hG hW hP
 have hnative := actualOriginalTransparentMinimumNativePreparation n arity q H G Q hq hH hG hQ
 have hs : GlobalSourcePackage.InputsCalibrated n arity s := hnative.2
 have ht := OriginalAllPositionStructuralTraversalRetentionProof.transparentCalibration n arity s H G W hs hH hG hW
 have hr : GlobalSourcePackage.InputsCalibrated n arity (refined p H G W P) :=
   OriginalVariableLeavesRefinementProof.refinedInputsCalibration n arity G _ hG ht
 have hprevious : OriginalRankGuardedRepresentative.Properties n arity q H G W :=
   ⟨transparentProperties n arity q H G W hq hH hG hW,
     actualOriginalRankGuardedRepresentativeLiteralFields q H G W,
     actualOriginalRankGuardedRepresentativeNativePreparation n arity q H G W hq hH hG hW,
     OriginalRankGuardedRepresentativeInternalProof.actualOriginalRankGuardedRepresentativeInternalRank q H G W,
     actualOriginalRankGuardedRepresentativeRetention n arity q H G W hq hH hG hW⟩
 have hret := actualOriginalTransparentMinimumRetention n arity q H G W Q hq hH hG hW hQ
 have hmin : OriginalTransparentMinimum.Properties n arity q H G W Q :=
   ⟨hprevious,hQ,actualOriginalTransparentMinimumLiteralFields q H G W Q,hnative,
     OriginalTransparentMinimumInternalReflexiveProof.actualOriginalTransparentMinimumInternalReflexive (OriginalTypedDecoder.target H G) Q,
     OriginalTransparentMinimumInternalScanProof.actualOriginalTransparentMinimumInternalScan _,
     OriginalTransparentMinimumGlobalProof.actualOriginalTransparentMinimumInternalMinimum (OriginalTypedDecoder.target H G) Q,
     OriginalTransparentMinimumGlobalProof.actualOriginalTransparentMinimumInternalGuardedClass q H G W Q,hret⟩
 have hfinal : OriginalFinalGuardedRank.Properties n arity s H G W :=
   ⟨hret,OriginalFinalGuardedRankCompletionProof.actualOriginalFinalGuardedTraversalRank s H G W,
     OriginalFinalGuardedRankCompletionProof.actualOriginalFinalGuardedFoldRank s H G W,
     OriginalFinalGuardedRankCompletionProof.actualOriginalFinalGuardedObjectRank s H G W⟩
 exact ⟨hprepared,hQ,hq,hs,hr,hmin,hfinal⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRetentionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRetentionProof
