module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenAssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

theorem actualApplication : EvaluatorChildrenTargets.ActualApplication := by
  intro R H G M W body alpha Delta left right domain codomain fn arg otherFn otherArg parameter had hl hr
  have sl := EvaluatorChildrenSourceProof.sourceApplication H G M W body alpha Delta
    left parameter domain codomain fn arg (andLeft had) hl
  have sr := EvaluatorChildrenSourceProof.sourceApplication H G M W body alpha Delta
    right parameter domain codomain otherFn otherArg (andLeft (andRight had)) hr
  have ql := EvaluatorChildrenSelectorProof.selectorApplication body alpha Delta
    left parameter domain codomain fn arg hl
  have qr := EvaluatorChildrenSelectorProof.selectorApplication body alpha Delta
    right parameter domain codomain otherFn otherArg hr
  exact EvaluatorChildrenAssemblyProof.application R H G M W
    left right parameter fn arg otherFn otherArg had
    (andLeft sl) (andRight sl) (andLeft sr) (andRight sr)
    (andLeft ql) (andLeft (andRight ql)) (andRight (andRight ql))
    (andLeft qr) (andLeft (andRight qr)) (andRight (andRight qr))

theorem actualLambda : EvaluatorChildrenTargets.ActualLambda := by
  intro R H G M W body alpha Delta left right domain codomain child otherChild parameter childParameter had hl hr
  have sl := EvaluatorChildrenSourceProof.sourceLambda H G M W body alpha Delta
    left parameter domain codomain child childParameter (andLeft had) hl
  have sr := EvaluatorChildrenSourceProof.sourceLambda H G M W body alpha Delta
    right parameter domain codomain otherChild childParameter (andLeft (andRight had)) hr
  have ql := EvaluatorChildrenSelectorProof.selectorLambda body alpha Delta
    left parameter domain codomain child childParameter hl
  have qr := EvaluatorChildrenSelectorProof.selectorLambda body alpha Delta
    right parameter domain codomain otherChild childParameter hr
  exact EvaluatorChildrenAssemblyProof.lambda R H G M W
    left right parameter child otherChild childParameter had sl sr
    (andLeft ql) (andLeft (andRight ql)) (andRight (andRight ql))
    (andLeft qr) (andLeft (andRight qr)) (andRight (andRight qr))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProof
