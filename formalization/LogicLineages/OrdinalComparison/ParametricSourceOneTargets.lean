module
public import LogicLineages.OrdinalComparison.ParametricSourceOneDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceOne.Targets
open SourceAdditionCompletion SourceSortCompletion

def IdentitySourceEquation : Prop :=
  (∀ Γ : List Ty, AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
    (.app (identity (Γ := Γ)) .zeroC) = some (identityVector Γ)) ∧
  ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
    ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (x : Variable Γ .ground),
      ParametricSourceAddition.Equation G ρ (successorProbe x) (.app identity .zeroC) ↔ input ρ x=2

def ExactOne : Prop := ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
  (∀ u v d : Nat, OneWitness G u v d ↔ u=1 ∧ v=2 ∧ d=3) ∧
  (∀ u : Nat, OneFormula G u ↔ u=1)

def ActualGammaOne : Prop := ∀ b : Nat,
  (∀ u v d : Nat, OneWitness (SourceMachineControlNonperiodicity.gamma b) u v d ↔ u=1 ∧ v=2 ∧ d=3) ∧
  (∀ u : Nat, OneFormula (SourceMachineControlNonperiodicity.gamma b) u ↔ u=1)
end LogicLineages.OrdinalComparison.Source.ParametricSourceOne.Targets
