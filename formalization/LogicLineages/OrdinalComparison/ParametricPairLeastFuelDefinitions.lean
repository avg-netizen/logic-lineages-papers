module
public import LogicLineages.OrdinalComparison.ParametricPairCollapseComputableDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel
noncomputable def leastFuel (H : Nat × Nat → Nat) (p : Nat × (Nat × Nat)) : Nat := by
  classical
  exact if h : ∃ fuel : Nat,(ParametricPairMachineCode.indexedEvaluate H p.1 p.2 fuel).isSome=true
    then Nat.find h else 0

def gammaControl (b : Nat) (p : Nat × Nat) : Nat :=
  SourceMachineControlNonperiodicity.gamma b p.2
noncomputable def gammaFuel (b : Nat) (p : Nat × Nat) : Nat := leastFuel (gammaControl b) (0,p)
end LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel
