module
public import LogicLineages.OrdinalComparison.WWTypedComponentDefinitions
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open SourceTypedPorts

def GroundPositiveTupleComplete : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) →
      ∃ xs : List Nat, xs.length = Γ.length ∧
        ∀ c, xs.getD (variableIndex c.2.1) 0 + 1 = ρ c

def GroundTuplePositive : Prop :=
  ∀ (Γ : List Ty) (xs : List Nat) (c : OrdinalComponent Γ),
    0 < xs.getD (variableIndex c.2.1) 0 + 1

def EmptyContextTupleUnique : Prop :=
  ∀ xs : List Nat, xs.length = ([] : List Ty).length ↔ xs = []
end LogicLineages.OrdinalComparison.Source.Targets
