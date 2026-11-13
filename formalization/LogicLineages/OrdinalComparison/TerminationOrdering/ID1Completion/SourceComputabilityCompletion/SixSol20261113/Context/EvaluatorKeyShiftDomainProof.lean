module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyShiftDomainTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyShiftDomainProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open EvaluatorKeyPut EvaluatorKeyDomainClosureSupportProof

theorem actualShiftDomain : EvaluatorKeyShiftDomainTargets.ActualShiftDomain := by
  intro p H G W body alpha Delta packed shifted d cutoff gamma extended c parameter extendedParameter hd hi hp hep hshift
  have hf := factors p H G W packed parameter hd
  have hs := OriginalTransparentDecoderFinalTransportSourceProof.sourceWeakeningAt
    H G (member p H G W) W d cutoff gamma extended c parameter extendedParameter packed shifted
    hi hp hep hshift (andRight hf)
  have hw := sameOuterWindow (prepared p H G W).window packed shifted parameter extendedParameter c gamma extended
    hp hep (andLeft hf)
  exact assemble p H G W shifted extendedParameter hw hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyShiftDomainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyShiftDomainProof
