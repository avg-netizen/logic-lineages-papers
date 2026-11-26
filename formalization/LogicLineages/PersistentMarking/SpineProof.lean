import LogicLineages.PersistentMarking.SpineTargets

namespace LogicLineages.PersistentMarking.SpineProof
open Spine

theorem emptyCall : SpineTargets.EmptyCall := by intro q; rfl
theorem freeBlocks : SpineTargets.FreeBlocks := by intro σ x a rest; simp [apply, applyAux]
theorem boundBlocks : SpineTargets.BoundBlocks := by intro σ i a rest; simp [apply, applyAux]
theorem binderCaptureAvoidance : SpineTargets.BinderCaptureAvoidance := by
  intro σ τ
  rfl
theorem retainedBinder : SpineTargets.RetainedBinder := by
  intro τ v
  rfl
theorem fullBlocked : SpineTargets.FullBlocked := by
  simp [SpineTargets.FullBlocked, SpineTargets.IdentityFunctional, SpineTargets.Successor,
    SpineTargets.GroundVariable, apply, applyAux, Expr.type, Head.result]
theorem stagedSucceeds : SpineTargets.StagedSucceeds := by
  simp [SpineTargets.StagedSucceeds, SpineTargets.IdentityFunctional, SpineTargets.Successor,
    SpineTargets.GroundVariable, apply, applyAux, Expr.type, Head.result, substitute,
    shift, shiftArgs, Args.get, substituteArgs, consumeTypes]

end LogicLineages.PersistentMarking.SpineProof
