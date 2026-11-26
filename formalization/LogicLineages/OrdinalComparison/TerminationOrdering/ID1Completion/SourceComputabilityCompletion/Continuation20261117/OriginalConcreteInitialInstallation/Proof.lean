module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteInitialInstallation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteInitialInstallation.Proof
open Continuation20261114 Continuation20261115 Continuation20261116
open UniformCertificateCompletion TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem concreteInitialTuple : Targets.ConcreteInitialTuple := by
  intro n arity p W hp hW
  let H := OriginalConcreteHeadSignature.signature n arity
  let G := OriginalDecodedContextValidity.contextGuard n
  let T := OriginalTypedDecoder.target H G
  let Q := OriginalCandidates.candidates n arity H
  let E := OriginalConcreteStructuralEdge.edge n arity
  let P := SeededPrimaryPool.pool T Q
  let L := SeededPrimaryPool.primary T Q E
  have hH := OriginalConcreteHeadSignature.NativeProof.nativeSignature n arity
  have hG : OriginalVariableLeaves.ContextGuardCalibrated n G :=
    OriginalDecodedContextValidity.NativeProof.nativeContext n
  have hT := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hQ := OriginalCandidates.NativeProof.nativeOriginal n arity H hH
  have hP := SeededPrimaryPool.NativeProof.poolCalibration n arity T Q hT hQ
  have hB := OriginalConcreteStructuralEdge.NativeProof.nativeStructural n arity
  have hE := TypedPrimaryEdge.NativeProof.edgeCalibration n arity
    (OriginalConcreteStructuralEdge.structural n arity) hB
  have hs : TransparentPrimary.SuppliersCalibrated n arity
      (LengthAlignedPrimary.countOfPool P) P E :=
    ⟨LengthAlignedPrimary.NativeProof.countCalibration n arity P hP,hP,hE⟩
  have hL : Membership.ListCalibrated n arity L :=
    TransparentPrimary.NativeProof.calibration n arity T
      (LengthAlignedPrimary.countOfPool P) P E hT hs
  exact ⟨hL,CandidateIntegration.Proof.retainedTuple n arity p H G W L hp hH hG hW hL⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteInitialInstallation.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteInitialInstallation.Proof
