module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionRunCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionLocalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof (andIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedClosedRecognitionInductionBindingProof

/-- Both local suppliers are actual proved closed-checker laws. The final
run theorem has no extra simulation or induction premise. -/
theorem acceptingRun : OriginalMixedClosedRecognitionTargets.AcceptingRun := by
 intro source H G M W oldStep window body alpha Delta out path state hr hf
 let leaf := OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window
 let outLeaf := OriginalTransparentMixedDirectBottom.leaf H G M W oldStep
 have hfinish : OriginalMixedClosedRecognitionRunCoreProof.FinishMap body source leaf outLeaf := by
  intro beta Theta final h
  exact OriginalMixedClosedRecognitionLocalProof.finishFactor source H G M W oldStep window
   body beta Theta final h
 have hstep : OriginalMixedClosedRecognitionRunCoreProof.StepMap body source leaf outLeaf := by
  intro beta Theta initial next ht hn
  exact OriginalMixedClosedRecognitionLocalProof.acceptedStep source H G M W oldStep window
   body beta Theta initial next ht hn
 exact atPathApply source leaf outLeaf path out state
  (OriginalMixedClosedRecognitionRunCoreProof.rows source leaf outLeaf hfinish hstep path)
  (andIntro hr hf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionRunProof
