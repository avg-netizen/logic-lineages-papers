module
public import LogicLineages.OrdinalComparison.ParametricExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricExistentialPlan.Targets
open ExistentialPlan

def ExactEquationRenaming : Prop := ∀ (G : Nat → Nat) (Γ Δ : List Ty) (r : Renaming Γ Δ)
  (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat),
  (∀ x,ν (r x)=ρ x) → ∀ a b : OriginalTerm Γ .ground,
    ParametricSourceAddition.Equation G (inputs ν) (a.rename r) (b.rename r) ↔
      ParametricSourceAddition.Equation G (inputs ρ) a b

def ExactCompilation : Prop := ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
  ∀ (Γ : List Ty) (q : Plan Γ), Supported q → ∀ ρ : Variable Γ .ground → Nat,
    EvalWith G ρ q ↔ ∃ ν : Variable (compile q).context .ground → Nat,
      (∀ x,ν ((compile q).embedding x)=ρ x) ∧ HoldsWith G (compile q) ν

def ActualGammaCompilation : Prop := ∀ (b : Nat) (Γ : List Ty) (q : Plan Γ), Supported q →
  ∀ ρ : Variable Γ .ground → Nat,
    EvalWith (SourceMachineControlNonperiodicity.gamma b) ρ q ↔
      ∃ ν : Variable (compile q).context .ground → Nat,
        (∀ x,ν ((compile q).embedding x)=ρ x) ∧
          HoldsWith (SourceMachineControlNonperiodicity.gamma b) (compile q) ν
end LogicLineages.OrdinalComparison.Source.ParametricExistentialPlan.Targets
