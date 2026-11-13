module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open EvaluatorKeyPut EvaluatorKeyDomainClosureSupportProof

theorem actualApplicationDomain : EvaluatorKeyApplicationDomainTargets.ActualApplicationDomain := by
  intro p H G W body alpha Delta parent parameter domain codomain fn arg hd hf
  have hparts := factors p H G W parent parameter hd
  have hchildren := EvaluatorChildrenSourceProof.sourceApplication H G (member p H G W) W
    body alpha Delta parent parameter domain codomain fn arg (andRight hparts) hf
  have hwf := OriginalApplicationSidecarWindowProof.windowTransfer
    (prepared p H G W).window _ parent fn parameter (andLeft hparts)
  have hwa := OriginalApplicationSidecarWindowProof.windowTransfer
    (prepared p H G W).window _ parent arg parameter (andLeft hparts)
  exact andIntro (assemble p H G W fn parameter hwf (andLeft hchildren))
    (assemble p H G W arg parameter hwa (andRight hchildren))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
