module
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeCalibrationProof
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeProgramsProof
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.Proof

theorem exactOutputs : Targets.ExactOutputs := by
  intro b e
  rcases exactSpine b e with ⟨hc,hs⟩
  constructor
  · unfold compiled
    rw [hc]
    exact (SourcePlanSpineCode.Proof.exactCompilation _ hs).2
  · unfold aggregate
    rw [hc]
    exact SourcePlanSpineCode.Proof.exactAggregate _ hs
end LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.Proof
