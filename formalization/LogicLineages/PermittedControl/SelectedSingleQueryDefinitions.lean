module
public import LogicLineages.PermittedControl.SelectedSeededSystemDefinitions
public import LogicLineages.PermittedControl.SelectedFiniteQueryDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSingleQuery
open OrdinalComparison Source SelectedSourceDomain Source.AdmissibleSum SelectedFiniteQuery
open Source.FunctionalHardnessCompletion (packGroundQuery encodedPolynomialSolvable)

def SingleQueryReduction (ctrl : Nat → Nat) (policy : Policy) (strict : Bool) : Prop :=
  ∃ reduce : Nat → Nat, Computable reduce ∧ ∀ e : Nat,
    ∃ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
      packGroundQuery a b=reduce e ∧ (∀ τ ∈ Γ, τ.level≤1) ∧
      SourceClasses.InternalLevelBound 3 a ∧ SourceClasses.InternalLevelBound 3 b ∧
      (¬encodedPolynomialSolvable e ↔
        ∀ ρ : AdmissibleSubstitution ctrl Γ, GroundComparison ctrl policy strict a b ρ)
end LogicLineages.PermittedControl.SelectedSingleQuery
