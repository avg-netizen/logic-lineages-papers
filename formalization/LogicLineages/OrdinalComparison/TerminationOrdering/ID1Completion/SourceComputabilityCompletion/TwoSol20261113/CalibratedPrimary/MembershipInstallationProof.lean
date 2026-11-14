module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipInstallationProof
open Membership MembershipNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualRetainedInstallation : MembershipTargets.ActualRetainedInstallation := by
  intro n arity p H G W L D hp hH hG hW hL hD
  have hT : TargetCalibrated n arity (OriginalTypedDecoder.target H G) :=
    OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hP := actualClassCalibration n arity (OriginalTypedDecoder.target H G) L D hT hL hD
  exact ⟨OriginalTransparentMinimumNativeProof.actualOriginalTransparentMinimumNativePreparation
      n arity p H G _ hp hH hG hP,
    OriginalTransparentMinimumNativeProof.actualOriginalTransparentMinimumRetention
      n arity p H G W _ hp hH hG hW hP⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipInstallationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipInstallationProof
