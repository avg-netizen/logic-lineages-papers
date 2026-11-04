module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedPrimaryWeakening
open NumberedStepWeakening NumberedTraceWeakeningSupportProof

theorem actualPackedTraceWeakeningReflection : NumberedTraceWeakeningTargets.ActualPackedTraceWeakeningReflection := by
  intro Symbol arity symbols S above Gamma sigma count q r h
  obtain ⟨target,he⟩ := NumberedTraceSupportProof.actualPackedTraceImage Symbol arity symbols S above Gamma (sigma :: Gamma)
    (Renaming.weaken Gamma sigma) count q r h
  refine ⟨target,he,?_⟩
  rw [← he] at h
  have hs := strictTrace (singleSubstitution (retractionFiller Symbol arity Gamma sigma))
    (NumberedStepWeakeningProof.fillerImages Symbol arity Gamma sigma) h
  simpa only [packedCancel] using hs

theorem actualTypedTraceWeakeningReflection : NumberedTraceWeakeningTargets.ActualTypedTraceWeakeningReflection := by
  intro Symbol arity symbols S above Gamma sigma tau count q r h
  obtain ⟨target,he⟩ := NumberedTraceSupportProof.actualTypedTraceImage Symbol arity symbols S above Gamma (sigma :: Gamma)
    (Renaming.weaken Gamma sigma) tau count q r h
  refine ⟨target,he,?_⟩
  rw [← he] at h
  have hp := (NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above (sigma :: Gamma) tau count _ _).mpr h
  have hs := strictTrace (singleSubstitution (retractionFiller Symbol arity Gamma sigma))
    (NumberedStepWeakeningProof.fillerImages Symbol arity Gamma sigma) hp
  change WindowTrace Symbol arity symbols S above Gamma count
    (NumberedPrimarySubstitution.substitutePacked (singleSubstitution (retractionFiller Symbol arity Gamma sigma)) (renamePacked (Renaming.weaken Gamma sigma) ⟨tau,q⟩))
    (NumberedPrimarySubstitution.substitutePacked (singleSubstitution (retractionFiller Symbol arity Gamma sigma)) (renamePacked (Renaming.weaken Gamma sigma) ⟨tau,target⟩)) at hs
  rw [packedCancel,packedCancel] at hs
  exact (NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above Gamma tau count q target).mp hs

theorem actualTupleTraceWeakeningReflection : NumberedTraceWeakeningTargets.ActualTupleTraceWeakeningReflection := by
  intro Symbol arity symbols S above Gamma sigma types count base target h
  obtain ⟨result,he⟩ := NumberedTraceSupportProof.actualTupleTraceImage Symbol arity symbols S above Gamma (sigma :: Gamma)
    (Renaming.weaken Gamma sigma) types count base target h
  refine ⟨result,he,?_⟩
  rw [← he] at h
  have hs := strictTupleTrace (singleSubstitution (retractionFiller Symbol arity Gamma sigma))
    (NumberedStepWeakeningProof.fillerImages Symbol arity Gamma sigma) h
  simpa only [NumberedRewriteApplicationBindingProof.weakeningArguments] using hs

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningProof
