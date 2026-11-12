module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedProof
open UniformCertificateCompletion OriginalMixedPrepared
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem literal (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Literal p H G W :=
 ⟨rfl,rfl⟩

theorem trace (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Trace p H G W := by
 change Trace p H G W
 exact OriginalMixedDirectBottomTraceTransportProof.actualRestrictedTransport H G (member p) W p.oldStep

/-- Native calibration pays only the prior package's calibration hypotheses.
The trace component comes from the independently checked internal theorem at a literal AST identity. -/
theorem actualRetention : OriginalMixedPreparedTargets.ActualRetention := by
 intro n arity p H G W P hp hH hG hW hP
 have hc := OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration
  n arity p H G W hp hH hG hW
 have hb := OriginalTransparentDirectBottomCalibrationProof.actualOriginalDirectBottomCalibration
  n arity (concrete p H G W) hc.1
 have hq := OriginalTransparentMixedPathProof.actualCalibration n arity (bottom p H G W) hb
 have he : ∀ v : List.Vector Nat 4, evaluate (prepared p H G W).oldStep v = evaluate p.oldStep v := by
  intro v
  exact (hq.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm
 have hk := OriginalActiveKernelMinimumGlobalProof.actualOriginalActiveKernelMinimumRetention
  n arity (prepared p H G W) H G W P hq hH hG hW hP
 exact ⟨hq,he,literal p H G W,hk,trace p H G W⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedProof
