module
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeCalibrationProof
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeProgramsProof
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.Proof

theorem exactAggregate : Targets.ExactAggregate := by
  intro Γ q hq
  unfold aggregateCode
  rw [run_correct q hq]
  have h := SourceGammaAggregateCode.Proof.exactAggregateCode (ExistentialPlan.compile q).context
    ((ExistentialPlan.compile q).forest.map (fun p => (p.1.term,p.2.term)))
  simpa only [compiledPairs,List.map_map,SourceGammaAggregateCode.pairCode,Function.comp_def] using h
end LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.Proof
