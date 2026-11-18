module
public import LogicLineages.PermittedControl.SelectedOmegaSeedDefinitions
public import LogicLineages.PermittedControl.SelectedPolynomialPatternsDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededCompilerDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededCompiler
open OrdinalComparison Source Source.SignedPair SelectedSourceDomain
open Source.FunctionalHardnessCompletion

noncomputable def seededInputs {n : Nat} (ctrl : Nat → Nat)
    (ρ : AdmissibleSubstitution ctrl (Context n)) (i : Fin (n+1)) : Ordinal :=
  if h : i.val<n then SelectedPairCompiler.inputs ctrl ρ ⟨i.val,h⟩
  else SelectedOmegaSeed.omega ctrl

def OrdinalSatisfiable (ctrl : Nat → Nat) {n : Nat} (s : System n) : Prop :=
  ∃ ρ : AdmissibleSubstitution ctrl (Context n),
    ∀ d ∈ s, meaning (seededInputs ctrl ρ) (SeededCompiler.subtractSeed d)=0
end LogicLineages.PermittedControl.SelectedSeededCompiler
