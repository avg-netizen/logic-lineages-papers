import LogicLineages.PersistentMarking.SpineTargets

namespace LogicLineages.PersistentMarking.SpineProof
open Spine

theorem emptyCall : SpineTargets.EmptyCall := by intro q; rfl
theorem freeBlocks : SpineTargets.FreeBlocks := by intro σ x a rest; rfl
theorem boundBlocks : SpineTargets.BoundBlocks := by intro σ i a rest; rfl
theorem binderCaptureAvoidance : SpineTargets.BinderCaptureAvoidance := by
  intro σ τ
  rfl
theorem retainedBinder : SpineTargets.RetainedBinder := by
  intro τ v
  rfl
theorem fullBlocked : SpineTargets.FullBlocked := by rfl
theorem stagedSucceeds : SpineTargets.StagedSucceeds := by rfl

end LogicLineages.PersistentMarking.SpineProof
