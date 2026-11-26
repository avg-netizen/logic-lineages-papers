module
public import LogicLineages.PermittedControl.SelectedGeneratedSourceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.GroundComparisonDomain
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain

/-- Paper 17 copy of Paper 18's `GroundDomain`, at a selected control: for a
context of ground variables, the admissible substitutions are exactly the
positive natural valuations of the context's components. -/
def SelectedGroundDomain : Prop :=
  ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
    (∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
      ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) →
        ∃ s : AdmissibleSubstitution ctrl Γ, ∀ c, valuation ctrl s c = (ρ c : Ordinal)) ∧
    (∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
      ∀ s : AdmissibleSubstitution ctrl Γ, ∃ ρ : OrdinalComponent Γ → Nat,
        (∀ c, 0 < ρ c) ∧ ∀ c, valuation ctrl s c = (ρ c : Ordinal))

end LogicLineages.PermittedControl.GroundComparisonDomain
