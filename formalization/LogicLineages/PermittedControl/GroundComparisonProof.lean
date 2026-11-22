module
public import LogicLineages.PermittedControl.GroundComparisonTargets
import LogicLineages.PermittedControl.GroundComparisonAssemblyProof
import LogicLineages.PermittedControl.GroundScalarCircuitCalibrationProof
import LogicLineages.PermittedControl.GroundScalarCircuitEffectivityProof

public section
namespace LogicLineages.PermittedControl.GroundComparison

/-- Paper 17 `thm:ground` comparator, unconditional. -/
theorem groundComparison : GroundComparison :=
  GroundComparisonAssembly.exactGroundFromQuery GroundScalarCircuit.queryCode
    GroundScalarCircuit.exactQueryCode GroundScalarCircuit.queryCodeEffectivity.to_comp

#print axioms groundComparison
end LogicLineages.PermittedControl.GroundComparison
