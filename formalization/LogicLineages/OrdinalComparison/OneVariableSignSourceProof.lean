module
public import LogicLineages.OrdinalComparison.OneVariableSignSourceTargets
public import LogicLineages.OrdinalComparison.ComparisonAssemblyLayerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneVariableSignSource

/-- ENTIRE literal two-sort eventual-sign theorem: the actual finite tree and
its bottom-up result table pay all comparison/gap/termination suppliers. -/
theorem full : Targets.FullActualOneVariableEventualSigns := by
  refine ⟨encodedOneVariableSignDecision,ComparisonAssembly.decision_program,?_⟩
  intro E F hE hF
  exact (ComparisonAssembly.result_correct ((oneVariableComparisonEncode E,oneVariableComparisonEncode F),(1,1))
    E F rfl rfl hE hF).1

end LogicLineages.OrdinalComparison.OneVariableSignSource
