module
public import LogicLineages.PermittedControl.SelectedHardnessDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPairCompiler
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain

/-- Actual selected-control inputs in precisely the original n-variable context. -/
noncomputable def inputs {n} (ctrl : Nat → Nat)
    (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)) (i : Fin n) : Ordinal :=
  closedValue ctrl (ρ.vector (SignedPair.inputVariable i) 1)

/-- Only the signed Cantor group is subtracted; both actual source fields are ordinals. -/
noncomputable def difference {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (q : SignedPair.Pair Γ) : SignedPair.CantorGroup :=
  SignedPair.signedCNF (SelectedHardness.value1 ctrl p ρ q.1) -
    SignedPair.signedCNF (SelectedHardness.value1 ctrl p ρ q.2)
end LogicLineages.PermittedControl.SelectedPairCompiler
