module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open EvaluatorKeyPut EvaluatorKeyDomainClosureSupportProof

theorem actualLambdaDomain : EvaluatorKeyDomainClosureTargets.ActualLambdaDomain := by
  intro p H G W body alpha Delta parent parameter domain codomain child childParameter hd hf
  have hparts := factors p H G W parent parameter hd
  have hs := EvaluatorChildrenSourceProof.sourceLambda H G (member p H G W) W
    body alpha Delta parent parameter domain codomain child childParameter (andRight hparts) hf
  have hw := OriginalLambdaTraversalLambdaWindowProof.windowChild
    (prepared p H G W).window _ parent child parameter childParameter
    (andRight (andRight (andRight (andRight hf)))) (andLeft hparts)
  exact assemble p H G W child childParameter hw hs

theorem actualErasureDomain : EvaluatorKeyDomainClosureTargets.ActualErasureDomain := by
  intro p H G W body alpha Delta packed out d cutoff gamma extended c oldParameter newParameter hd hi hop hnp he
  have hparts := factors p H G W packed oldParameter hd
  have hs := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure
    body alpha Delta H G (member p H G W) W packed out d cutoff gamma extended c oldParameter newParameter
    hi he hop hnp (andRight hparts)
  have hw := sameOuterWindow (prepared p H G W).window packed out oldParameter newParameter c extended gamma
    hop hnp (andLeft hparts)
  exact assemble p H G W out newParameter hw hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureProof
