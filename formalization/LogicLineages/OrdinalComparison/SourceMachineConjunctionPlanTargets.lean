module
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Targets
open ExistentialPlan ParametricExistentialPlan

def SupportedSyntax : Prop := ∀ b e : Nat, Supported (plan b e)

def ExactConjunction : Prop := ∀ (b e : Nat) (ρ : Variable Base .ground → Nat),
  EvalWith (SourceMachineControlNonperiodicity.gamma b) ρ (plan b e) ↔
    SourceMachineHaltingConjunction.Conjunction b e
      (ρ (original 0)) (ρ (original 1)) (ρ (original 2)) (ρ (original 3))

def ExactCompiledHalting : Prop :=
  (∀ (b e : Nat) (ρ : Variable Base .ground → Nat),
    (∃ ν : Variable (compile (plan b e)).context .ground → Nat,
      (∀ x,ν ((compile (plan b e)).embedding x)=ρ x) ∧
      HoldsWith (SourceMachineControlNonperiodicity.gamma b) (compile (plan b e)) ν) ↔
    SourceMachineHaltingConjunction.Conjunction b e
      (ρ (original 0)) (ρ (original 1)) (ρ (original 2)) (ρ (original 3))) ∧
  (∀ b e : Nat,
    (∃ ν : Variable (compile (plan b e)).context .ground → Nat,
      HoldsWith (SourceMachineControlNonperiodicity.gamma b) (compile (plan b e)) ν) ↔
      SourceBlankMachineSimulation.Halts e)

def ExactCompiledBounds : Prop := ∀ b e : Nat,
  (compile (plan b e)).nodes ≤ 80*(e+4*bits b+27)+4 ∧
  (compile (plan b e)).forest.length ≤ 10*(e+4*bits b+27)+1 ∧
  (compile (plan b e)).context.length ≤ 4+10*e+40*bits b+268
end LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Targets
