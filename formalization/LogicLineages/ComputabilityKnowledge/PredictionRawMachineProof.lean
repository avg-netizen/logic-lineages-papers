module

public import LogicLineages.ComputabilityKnowledge.PredictionRawMachineTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRawMachineProof
open PredictionRawMachine PredictionRawMachineTargets

private theorem update_input (xs ys zs : List Bool) :
    Function.update (fun b : Bool => if b then ys else xs) false zs =
      (fun b : Bool => if b then ys else zs) := by
  funext b
  cases b <;> simp

private theorem update_output (xs ys zs : List Bool) :
    Function.update (fun b : Bool => if b then ys else xs) true zs =
      (fun b : Bool => if b then zs else xs) := by
  funext b
  cases b <;> simp

theorem rawZeroTransition : RawZeroTransition := by
  intro k i hi state xs ys
  simp [machineStep, runningCfg, terminalCfg, evaderStmt, hi,
    Turing.TM2.step, Turing.TM2.stepAux, update_output]

theorem rawNonemptyTransition : RawNonemptyTransition := by
  intro k i hi state a xs ys
  have hn : i.val ≠ 0 := Nat.ne_of_gt hi
  simp [machineStep, runningCfg, evaderStmt, hn, Turing.TM2.step,
    Turing.TM2.stepAux, update_input]

theorem rawEmptyTransition : RawEmptyTransition := by
  intro k i hi state ys
  have hn : i.val ≠ 0 := Nat.ne_of_gt hi
  simp [machineStep, runningCfg, terminalCfg, evaderStmt, hn,
    Turing.TM2.step, Turing.TM2.stepAux, update_input, update_output]

theorem rawTerminalTransition : RawTerminalTransition := by
  intro k state xs ys
  rfl

end LogicLineages.ComputabilityKnowledge.PredictionRawMachineProof
