module
public import LogicLineages.PermittedControl.SelectedSourceDomainDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardDomainCalibration
open OrdinalComparison Source

/-- Equality of the actual closed-expression vectors, including every coordinate. -/
def SameVector {Γ : List Ty} (ρ : SelectedSourceDomain.AdmissibleSubstitution Phi Γ)
    (σ : OriginalDomain.AdmissibleSubstitution Γ) : Prop :=
  ∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)), ρ.vector x j=σ.vector x j
end LogicLineages.PermittedControl.StandardDomainCalibration
