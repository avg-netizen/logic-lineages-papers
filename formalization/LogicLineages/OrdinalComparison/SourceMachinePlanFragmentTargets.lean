module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFragmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment.Targets
open ExistentialPlan BinaryPlan PrimitiveLowering ParametricScalingPlan SourceGroundBinderFragment

def RenamePreservation : Prop := ∀ (Γ Δ : List Ty) (r : Renaming Γ Δ) (q : Plan Γ),
  PlanFragment q → PlanFragment (renamePlan r q)

def ConstructorPreservation : Prop :=
  (∀ (Γ : List Ty) (d : SourceAdditionCompletion.BinaryDAG) (out : Port Γ) (q : Plan Γ),
    PlanFragment q → PlanFragment (binaryPlan d out q)) ∧
  (∀ (Γ : List Ty) (k : Nat) (q : Plan (.ground::Γ)),
    PlanFragment q → PlanFragment (constantPlan k q)) ∧
  (∀ (Γ : List Ty) (e : Nat) (a out : Port Γ) (q : Plan Γ),
    PlanFragment q → PlanFragment (scalePlan e a out q))

def CompilerPreservation : Prop := ∀ (Γ : List Ty) (q : Plan Γ), PlanFragment q →
  ∀ f ∈ (compile q).forest, Fragment f.1.term ∧ Fragment f.2.term

def ActualAggregateFragment : Prop := ∀ b e : Nat,
  PlanFragment (SourceMachineConjunctionPlan.plan b e) ∧
  Fragment (SourceMachineAggregateBridge.aggregate b e).1 ∧
  Fragment (SourceMachineAggregateBridge.aggregate b e).2
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment.Targets
