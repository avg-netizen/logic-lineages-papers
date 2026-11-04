module
public import LogicLineages.OrdinalComparison.SourceMachineLogarithmicDAGTargets
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanSizeProof
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceMachineLogarithmicDAG.Proof

theorem bitsBound : Targets.BitsBound := by
  intro b
  have hlog : Nat.log 2 (2*b+5) ≤ Nat.log 2 ((b+2)*2*2) :=
    Nat.log_mono_right (by omega)
  rw [Nat.log_mul_base (b := 2) (n := (b+2)*2) (by decide) (by omega),
    Nat.log_mul_base (b := 2) (n := b+2) (by decide) (by omega)] at hlog
  change Nat.log2 (2*b+5)+1 ≤ Nat.log2 (b+2)+3
  simp only [Nat.log2_eq_log_two]
  omega

theorem compiledBounds : Targets.CompiledBounds := by
  intro b e
  have hb := bitsBound b
  have hc := SourceMachineConjunctionPlan.Proof.exactCompiledBounds b e
  exact ⟨by omega, by omega, by omega⟩

end LogicLineages.OrdinalComparison.Source.SourceMachineLogarithmicDAG.Proof
