module
public import LogicLineages.OrdinalComparison.ParametricPairCollapseComputableDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairCollapseComputable.Targets

def ExactSearch : Prop := ∀ (H : Nat × Nat → Nat) (p : Nat × (Nat × Nat)),
  actualValue H p ∈ searchValue H p ∧ (searchValue H p).Dom ∧
  (∀ n : Nat, n ∈ searchValue H p ↔ n=actualValue H p) ∧
  ∃ fuel : Nat,
    ParametricPairMachineCode.indexedEvaluate H p.1 p.2 fuel=some (actualValue H p) ∧
    (∀ k<fuel, ParametricPairMachineCode.indexedEvaluate H p.1 p.2 k=none)

def UniformPartialRecursive : Prop := ∀ H : Nat × Nat → Nat,
  Computable H → Partrec (searchValue H)

def UniformComputable : Prop := ∀ H : Nat × Nat → Nat,
  Computable H → Computable (actualValue H)

def FixedGammaComputable : Prop := ∀ b : Nat,
  Computable (ParametricFinitePairCollapse.value (SourceMachineControlNonperiodicity.gamma b))
end LogicLineages.OrdinalComparison.Source.ParametricPairCollapseComputable.Targets
