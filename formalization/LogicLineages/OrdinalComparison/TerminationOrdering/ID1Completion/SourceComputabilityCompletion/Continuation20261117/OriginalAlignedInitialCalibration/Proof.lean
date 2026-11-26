module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialCalibration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteInitialInstallation.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialCalibration.Proof
open UniformCertificateCompletion
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalOriginalUniformParameterLeaves

theorem liftedMember (n : Nat) (v : List.Vector Nat 2) :
    evaluate (OriginalContextMemberLift.liftMember (OriginalUniverseDomainCoverage.member n)) v = memberValue n v := by
  change evaluate (OriginalUniverseDomainCoverage.member n)
    (ofFn ![v.get 0,evaluate (leftOf (.projection 1)) v]) = memberValue n v
  rw [leftOfEvaluation,OriginalUniverseDomainCoverage.NativeProof.nativeOriginalMember]
  simp only [projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]
  obtain ⟨gamma,hgamma⟩ := InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
    (v.get 0) (v.get 1)
  unfold memberValue decodedValue
  rw [hgamma]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1 <;>
    simp only [hc,OriginalUniverseDecoder.contextMemberValue]

theorem aligned (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (OriginalAlignedInitialSource.alignedInputs n p) :=
  ⟨⟨hp.1.1,hp.1.2.1,hp.1.2.2.1,liftedMember n⟩,hp.2⟩

theorem nativeAlignedCalibration : Targets.NativeAlignedCalibration := by
  intro n arity p hp
  have hpa := aligned n arity p hp
  let H := OriginalConcreteHeadSignature.signature n arity
  let G := OriginalDecodedContextValidity.contextGuard n
  let W := OriginalGuardedHeadSourceCoverage.window n arity
  let T := OriginalTypedDecoder.target H G
  let L := SeededPrimaryPool.primary T (OriginalCandidates.candidates n arity H) (OriginalConcreteStructuralEdge.edge n arity)
  let q := TwoSol20261113.CalibratedPrimary.Membership.inputs (OriginalAlignedInitialSource.alignedInputs n p) H G L (TransparentCandidate.candidate T)
  have hH := OriginalConcreteHeadSignature.NativeProof.nativeSignature n arity
  have hG := OriginalDecodedContextValidity.NativeProof.nativeContext n
  have hW := OriginalGuardedHeadSourceCoverage.NativeProof.nativeOriginalWindow n arity
  have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
    (OriginalConcreteInitialInstallation.Proof.concreteInitialTuple n arity
      (OriginalAlignedInitialSource.alignedInputs n p) W hpa hW).2.2.1
  have hg := OriginalRankGuardedRepresentativeNativeProof.actualOriginalRankGuardedRepresentativeNativePreparation
    n arity q H G W hq hH hG hW
  have ht := OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration
    n arity (OriginalRankGuardedRepresentative.guardedInputs H G W q) H G W hg.2 hH hG hW
  exact ⟨hpa,ht.1⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialCalibration.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialCalibration.Proof
