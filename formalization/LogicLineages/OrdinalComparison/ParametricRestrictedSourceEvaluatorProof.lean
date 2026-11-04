module
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorProgramsProof
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorCalibrationProof
public import LogicLineages.OrdinalComparison.SourceMachinePlanFragmentProof
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsCoordinatesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator.Proof

theorem generatedAggregate : Targets.GeneratedAggregate := by
  intro b e xs hlen
  have hg := SourceMachineRawValuations.Proof.groundContexts.2 b e
  have hf := (SourceMachinePlanFragment.Proof.actualAggregateFragment b e).2
  let H : Nat × Nat → Nat := fun p => SourceMachineControlNonperiodicity.gamma b p.2
  have hl := typedCalibration H 0 _ (SourceMachineAggregateBridge.aggregate b e).1 xs hg hf.1 hlen
  have hr := typedCalibration H 0 _ (SourceMachineAggregateBridge.aggregate b e).2 xs hg hf.2 hlen
  obtain ⟨l,hel⟩ := hl.1
  obtain ⟨r,her⟩ := hr.1
  refine ⟨l,r,?_,?_,(hl.2 l).mp hel,(hr.2 r).mp her⟩
  · simpa only [gammaEvaluate,hlen] using hel
  · simpa only [gammaEvaluate,hlen] using her
end LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator.Proof
