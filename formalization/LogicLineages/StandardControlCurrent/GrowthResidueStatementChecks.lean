module
public import LogicLineages.StandardControlCurrent.GrowthResidueTargets
public import LogicLineages.OrdinalComparison.ControlResidueProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GrowthResidueStatementChecks
open OrdinalComparison

theorem growth : GrowthResidueTargets.FullFastControlHierarchyGrowth :=
  fullFastControlHierarchyGrowth

theorem residues : GrowthResidueTargets.FullFastControlConstantResidues :=
  fullFastControlConstantResidues

#print axioms growth
#print axioms residues

end LogicLineages.StandardControlCurrent.GrowthResidueStatementChecks
