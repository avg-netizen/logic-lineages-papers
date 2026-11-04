module
public import LogicLineages.OrdinalComparison.ParametricPairMachineCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairCollapseComputable
def searchValue (H : Nat × Nat → Nat) (p : Nat × (Nat × Nat)) : Part Nat :=
  Nat.rfindOpt (ParametricPairMachineCode.indexedEvaluate H p.1 p.2)
noncomputable def actualValue (H : Nat × Nat → Nat) (p : Nat × (Nat × Nat)) : Nat :=
  ParametricFinitePairCollapse.value (fun n => H (p.1,n)) p.2
end LogicLineages.OrdinalComparison.Source.ParametricPairCollapseComputable
