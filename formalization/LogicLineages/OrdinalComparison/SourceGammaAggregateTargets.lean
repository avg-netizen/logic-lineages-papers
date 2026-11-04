module
public import LogicLineages.OrdinalComparison.SourceGammaAggregateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregate.Targets
open ParametricSourceEraser SourceAggregateCompletion

def EquationCalibration : Prop :=
  (∀ (G : Nat → Nat) (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal)
    (p q : OriginalTerm Γ .ground) (x y : Nat),
    Scalar G ν p x → Scalar G ν q y → (Equal G ν p q ↔ x=y)) ∧
  (∀ (G : Nat → Nat) (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal),
    Scalar G ν (.zeroC : OriginalTerm Γ .ground) 1)

def FiniteAggregate : Prop := ∀ (b : Nat) (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)), FiniteLeaves b ν es →
  ∃ l r : Nat,
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν (aggregate es).1 l ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν (aggregate es).2 r ∧
    r ≤ l ∧ (l=r ↔ SourceGammaAggregate.AllEqual b ν es) ∧
    (¬ SourceGammaAggregate.AllEqual b ν es → 2 ≤ l-r)

def NaturalEquationAggregate : Prop := ∀ (b : Nat) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)),
  FiniteLeaves b (fun c => ((ρ c+1 : Nat) : Ordinal)) es →
  ∃ l r : Nat,
    Scalar (SourceMachineControlNonperiodicity.gamma b) (fun c => ((ρ c+1 : Nat) : Ordinal)) (aggregate es).1 l ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) (fun c => ((ρ c+1 : Nat) : Ordinal)) (aggregate es).2 r ∧
    r ≤ l ∧ (l=r ↔ ∀ e ∈ es,ParametricSourceAddition.Equation (SourceMachineControlNonperiodicity.gamma b) ρ e.1 e.2) ∧
    ((¬ ∀ e ∈ es,ParametricSourceAddition.Equation (SourceMachineControlNonperiodicity.gamma b) ρ e.1 e.2) → 2 ≤ l-r)
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregate.Targets
