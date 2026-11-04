module
public import LogicLineages.OrdinalComparison.SourceMachineLogarithmicDAGDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineLogarithmicDAG.Targets

def BitsBound : Prop := ∀ b : Nat,
  SourceMachineConjunctionPlan.bits b ≤ Nat.log2 (b+2)+3

def CompiledBounds : Prop := ∀ b e : Nat,
  (ExistentialPlan.compile (SourceMachineConjunctionPlan.plan b e)).nodes ≤
    80*(e+4*Nat.log2 (b+2)+39)+4 ∧
  (ExistentialPlan.compile (SourceMachineConjunctionPlan.plan b e)).forest.length ≤
    10*(e+4*Nat.log2 (b+2)+39)+1 ∧
  (ExistentialPlan.compile (SourceMachineConjunctionPlan.plan b e)).context.length ≤
    10*e+40*Nat.log2 (b+2)+392
end LogicLineages.OrdinalComparison.Source.SourceMachineLogarithmicDAG.Targets
