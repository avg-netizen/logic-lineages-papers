module
public import LogicLineages.OrdinalComparison.ParametricPairLeastFuelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel.Targets

def ExactLeastFuel : Prop := ∀ (H : Nat × Nat → Nat) (p : Nat × (Nat × Nat)),
  ParametricPairMachineCode.indexedEvaluate H p.1 p.2 (leastFuel H p)=
    some (ParametricPairCollapseComputable.actualValue H p) ∧
  (∀ k : Nat,k<leastFuel H p → ParametricPairMachineCode.indexedEvaluate H p.1 p.2 k=none) ∧
  (∀ (k n : Nat),ParametricPairMachineCode.indexedEvaluate H p.1 p.2 k=some n → leastFuel H p≤k)

def UniformComputable : Prop := ∀ H : Nat × Nat → Nat,
  Computable H → Computable (leastFuel H)

def FixedGammaFuel : Prop := ∀ b : Nat, Computable (gammaFuel b) ∧
  ∀ p : Nat × Nat,
    ParametricPairWorklist.evaluate (SourceMachineControlNonperiodicity.gamma b) p (gammaFuel b p)=
      some (ParametricFinitePairCollapse.value (SourceMachineControlNonperiodicity.gamma b) p) ∧
    ∀ k : Nat,k<gammaFuel b p →
      ParametricPairWorklist.evaluate (SourceMachineControlNonperiodicity.gamma b) p k=none
end LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel.Targets
