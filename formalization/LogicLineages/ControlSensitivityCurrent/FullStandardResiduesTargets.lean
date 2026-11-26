module
public import LogicLineages.OrdinalComparison.ControlResidueTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullStandardResidues.Targets
open LogicLineages.OrdinalComparison
/-- Complete current19 standard residues with a fixed genuinely effective witness. -/
def CompleteResidues : Prop :=
  (∀ m : Nat, 0 < m → fastControlResidue m < m) ∧
  Primrec fastControlResidue ∧
  (∀ m : Nat, 0 < m → ∀ j n : Nat, 1 ≤ j → m ≤ n →
    Nat.ModEq m (fastControl j n) (fastControlResidue m)) ∧
  (∀ m : Nat, 0 < m → ∀ t : Nat, m - 100 ≤ t →
    Nat.ModEq m (Phi t) (fastControlResidue m))
end LogicLineages.ControlSensitivityCurrent.FullStandardResidues.Targets
