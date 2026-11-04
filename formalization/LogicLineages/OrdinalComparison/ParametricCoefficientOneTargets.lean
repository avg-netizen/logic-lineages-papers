module
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricCoefficientOne.Targets

def GenericCoefficientOne : Prop := ∀ G : Nat → Nat,
  StrictMono G → (∀ n : Nat, n ≤ G n) →
  ∀ n : Nat, coefficientOne G n = G (n+2)+1

def ActualGammaCoefficientOne : Prop := ∀ b : Nat,
  StrictMono (SourceMachineControlNonperiodicity.gamma b) ∧
  (∀ n : Nat, n ≤ SourceMachineControlNonperiodicity.gamma b n) ∧
  ∀ n : Nat, coefficientOne (SourceMachineControlNonperiodicity.gamma b) n =
    SourceMachineControlNonperiodicity.gamma b (n+2)+1
end LogicLineages.OrdinalComparison.ParametricCoefficientOne.Targets
