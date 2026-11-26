module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionSuccessProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
open LogicLineages.OrdinalComparison.Source
open Operations

theorem application_size (t : Nat) (f a : Code) :
    (applicationRaw t f a).2.1.length=f.2.1.length+a.2.1.length+1 := by
  simp [applicationRaw,appendTable,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
theorem eraser_size (a b : Code) :
    (eraserRaw a b).2.1.length=a.2.1.length+b.2.1.length+2 := by
  simp [eraserRaw,appendTable,insertTable,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem application_result (t : Nat) (f a co : Code) (h : application t f a=some co) :
    co=applicationRaw t f a := by
  unfold application at h
  split at h
  next hg => exact (Option.some.inj h).symm
  next hg => simp at h

theorem eraser_result (a b co : Code) (h : eraser a b=some co) : co=eraserRaw a b := by
  unfold eraser at h
  split at h
  next hg => exact (Option.some.inj h).symm
  next hg => simp at h

theorem rejectionAndCounts : RawCheckedCompositionTargets.RejectionAndCounts := by
  refine ⟨?_,?_,application_size,eraser_size,?_,?_⟩
  · intro t f a
    cases hg : applicationGuard t f a <;> simp [application,hg]
  · intro a b
    cases hg : eraserGuard a b <;> simp [eraser,hg]
  · intro t f a co h
    have hv : valid co=true := by
      obtain ⟨Γ,σ,τ,ff,aa,ht,hf,ha,ho,hd⟩ := application_success t f a co h
      rw [← ho]
      exact typedAccepted _
    refine ⟨hv,?_⟩
    rw [application_result t f a co h]
    exact ⟨rfl,rfl,rfl,application_size t f a⟩
  · intro a b co h
    have hv : valid co=true := by
      obtain ⟨Γ,aa,bb,ha,hb,ho,hd⟩ := eraser_success a b co h
      rw [← ho]
      exact typedAccepted _
    refine ⟨hv,?_⟩
    rw [eraser_result a b co h]
    exact ⟨rfl,rfl,rfl,eraser_size a b⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
