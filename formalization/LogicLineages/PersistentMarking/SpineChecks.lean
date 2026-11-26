import LogicLineages.PersistentMarking.SpineProof

namespace LogicLineages.PersistentMarking.SpineChecks

theorem emptyCall : SpineTargets.EmptyCall := SpineProof.emptyCall
theorem freeBlocks : SpineTargets.FreeBlocks := SpineProof.freeBlocks
theorem boundBlocks : SpineTargets.BoundBlocks := SpineProof.boundBlocks
theorem binderCaptureAvoidance : SpineTargets.BinderCaptureAvoidance := SpineProof.binderCaptureAvoidance
theorem retainedBinder : SpineTargets.RetainedBinder := SpineProof.retainedBinder
theorem fullBlocked : SpineTargets.FullBlocked := SpineProof.fullBlocked
theorem stagedSucceeds : SpineTargets.StagedSucceeds := SpineProof.stagedSucceeds

#print axioms emptyCall
#print axioms freeBlocks
#print axioms boundBlocks
#print axioms binderCaptureAvoidance
#print axioms retainedBinder
#print axioms fullBlocked
#print axioms stagedSucceeds
end LogicLineages.PersistentMarking.SpineChecks
