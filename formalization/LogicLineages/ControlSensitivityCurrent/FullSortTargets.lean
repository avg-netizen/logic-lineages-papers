module
public import LogicLineages.ControlSensitivityCurrent.PolicySortDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
public import LogicLineages.ControlSensitivityCurrent.PairCodingTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullSort.Targets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion
/-- Complete current19 lem:sort: derive growth, actual S calibration and joint PP sort. -/
def CompleteSort : Prop := ∀ f : Nat → Nat, FullAddition.Targets.SourceGrowth f →
  (∀ n : Nat, 0 < f (n+4) ∧ 2 * f (n+4) < f (n+1+4)) ∧
  (∀ a b c d : Nat, f (a+4) + f (b+4) = f (c+4) + f (d+4) ↔
    ({a,b} : Multiset Nat) = {c,d}) ∧
  ∀ p : AdmissibleSum.Policy,
    (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (x : Variable Γ .ground) (y : Nat),
      PolicySort.Observation p f ρ (successorProbe x) y ↔ y = f (input ρ x+4)) ∧
    (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (a b low high : Variable Γ .ground)
      (difference : Nat), PolicySort.SortFormula p f ρ a b low high difference ↔
        input ρ low = min (input ρ a) (input ρ b) ∧
        input ρ high = max (input ρ a) (input ρ b) ∧
        difference = max (input ρ a) (input ρ b) - min (input ρ a) (input ρ b))
end LogicLineages.ControlSensitivityCurrent.FullSort.Targets
