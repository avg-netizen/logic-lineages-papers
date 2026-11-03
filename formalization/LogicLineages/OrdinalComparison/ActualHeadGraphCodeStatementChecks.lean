module
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeTargets
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.StatementChecks
theorem exact_genuine_constants : Targets.ExactGenuineConstants := Proof.exactGenuineConstants
theorem exact_formula_compilation : Targets.ExactFormulaCompilation := Proof.exactFormulaCompilation
theorem effective_algorithms : Targets.EffectiveAlgorithms := Proof.effectiveAlgorithms
theorem actual_effective_whole_graph : Targets.ActualEffectiveWholeGraph := Proof.actualEffectiveWholeGraph
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode
