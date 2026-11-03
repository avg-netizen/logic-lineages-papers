module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerCallProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler.Proof

theorem allCodeComputation : Targets.AllCodeComputation := by
  obtain ⟨hbase, hchildren, hassemble, hmeasure⟩ := numericalInterfaces
  obtain ⟨hleaf, hactual, hchild, hdecrease, hequation⟩ := exactFiniteCallEquation
  exact BalancedBoxEvaluation.Graph.exactDecreasingGraph Input Code children assemble measure
    hchildren hassemble hmeasure recursiveCode hdecrease hequation

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler.Proof
