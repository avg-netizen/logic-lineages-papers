module
public import LogicLineages.StandardControlCurrent.SingleCoreTargets
public import LogicLineages.OrdinalComparison.SingleCorePresburgerProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.SingleCoreStatementChecks
open OrdinalComparison

theorem programs : SingleCoreTargets.Programs := SingleCorePresburger.programs

theorem signFormulas : SingleCoreTargets.SignFormulas := SingleCorePresburger.output

theorem universalComparison : SingleCoreTargets.UniversalComparison :=
  SingleCorePresburger.universal_correct

theorem full : SingleCoreTargets.FullSingleCore :=
  ⟨programs, signFormulas, universalComparison⟩

#print axioms programs
#print axioms signFormulas
#print axioms universalComparison
#print axioms full

end LogicLineages.StandardControlCurrent.SingleCoreStatementChecks
