module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepTermProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryReturnStep OriginalHereditaryReturnStepSupportProof OriginalHereditaryReturnStepEvaluationProof

theorem termReturn : OriginalHereditaryReturnStepTargets.TermReturn := by
  intro R Q n arity Gamma c q deletions agenda old hd
  rw [← hd,stateCons,termJob,termDispatch,popEvaluation,termEvaluation]
  have hc := OriginalHereditaryResultStackProgramProof.calibration (termChildren Q c q) deletions old
    (termChildrenBound Q c q)
  dsimp only at hc
  rw [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  have hslots := termChildrenSlots Q c q
  have hfirst := congrArg Prod.fst hslots
  have hsecond := congrArg Prod.snd hslots
  dsimp only at hfirst hsecond
  rw [hfirst,hsecond]
  have hp : Nat.pair (typeNumber q.1) (codeNumber (NumberedAuxiliaryCoding.termCode q.2)) = packedNumber q := rfl
  rw [hp,OriginalHereditaryReturnNativeProof.rootSubstitution]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepTermProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepTermProof
