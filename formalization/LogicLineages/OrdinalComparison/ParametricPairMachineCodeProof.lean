module
public import LogicLineages.OrdinalComparison.ParametricPairMachineCodeIterationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode.Proof
open ParametricFinitePairCollapse ParametricPairWorklist

theorem children_calibration (H : Nat × Nat → Nat) (i : Nat) (p : Nat × Nat) :
    childrenBudget p (H (i,pairNorm p))=children (fun n => H (i,n)) p := rfl

theorem step_calibration (H : Nat × Nat → Nat) (i : Nat) (s : State) :
    indexedStep H i s=step (fun n => H (i,n)) s := by
  rcases s with ⟨ts,vs⟩
  cases ts with
  | nil => rfl
  | cons t ts => cases t <;> rfl

theorem run_calibration (H : Nat × Nat → Nat) (i fuel : Nat) (s : State) :
    indexedRun H i fuel s=run (fun n => H (i,n)) fuel s := by
  have h : indexedStep H i=step (fun n => H (i,n)) := funext (step_calibration H i)
  simp only [indexedRun,run,h]

theorem exactCalibration : Targets.ExactCalibration := by
  intro H
  refine ⟨children_calibration H,step_calibration H,run_calibration H,?_⟩
  intro i p fuel
  simp only [indexedEvaluate,evaluate,run_calibration]
end LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode.Proof
