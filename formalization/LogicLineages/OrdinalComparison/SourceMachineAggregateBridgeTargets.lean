module
public import LogicLineages.OrdinalComparison.SourceMachineAggregateBridgeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineAggregateBridge.Targets
open ExistentialPlan ParametricExistentialPlan ParametricSourceEraser ParametricPrimitiveFinite

def PointwiseAggregate : Prop := ∀ (b e : Nat)
    (ρ : Variable (compile (SourceMachineConjunctionPlan.plan b e)).context .ground → Nat),
  ∃ l r : Nat,
    Scalar (SourceMachineControlNonperiodicity.gamma b) (positive (inputs ρ)) (aggregate b e).1 l ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) (positive (inputs ρ)) (aggregate b e).2 r ∧
    r ≤ l ∧
    (l=r ↔ HoldsWith (SourceMachineControlNonperiodicity.gamma b)
      (compile (SourceMachineConjunctionPlan.plan b e)) ρ) ∧
    (¬ HoldsWith (SourceMachineControlNonperiodicity.gamma b)
      (compile (SourceMachineConjunctionPlan.plan b e)) ρ → 2 ≤ l-r)

def ExistentialEquality : Prop := ∀ b e : Nat,
  (∃ ρ : Variable (compile (SourceMachineConjunctionPlan.plan b e)).context .ground → Nat,
    SourceGammaAggregate.Equal (SourceMachineControlNonperiodicity.gamma b) (positive (inputs ρ))
      (aggregate b e).1 (aggregate b e).2) ↔ SourceBlankMachineSimulation.Halts e

def UniversalStrictNonhalting : Prop := ∀ b e : Nat,
  UniversalStrict b e ↔ ¬ SourceBlankMachineSimulation.Halts e
end LogicLineages.OrdinalComparison.Source.SourceMachineAggregateBridge.Targets
