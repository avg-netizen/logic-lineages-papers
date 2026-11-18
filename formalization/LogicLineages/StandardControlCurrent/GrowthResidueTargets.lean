module
public import LogicLineages.OrdinalComparison.ControlResidueDefinitions
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Data.Nat.ModEq

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GrowthResidueTargets
open OrdinalComparison

/-! Full current18 m:lem:growth and m:lem:residues, with actual fixed
variable-seed hierarchy and concrete effective residue, no supplier premise. -/

def FullFastControlHierarchyGrowth : Prop :=
  (∀ j : Nat, Computable (fastControl j) ∧ StrictMono (fastControl j) ∧
    ∀ n : Nat, 2 ^ n ≤ fastControl j n) ∧
  (∀ j n : Nat, 2 ^ (fastControl (j + 1) n + 1) ≤ fastControl (j + 1) (n + 1)) ∧
  (∀ A z : Nat, A ≤ z → (A + 2) * Phi z ≤ Phi (z + 1))

def FastControlResidueRange : Prop := ∀ m : Nat, 0 < m → fastControlResidue m < m

def FastControlResiduePrimitiveRecursive : Prop := Primrec fastControlResidue

def FastControlConstantResidues : Prop :=
  ∀ m : Nat, 0 < m → ∀ j n : Nat, 1 ≤ j → m ≤ n →
    Nat.ModEq m (fastControl j n) (fastControlResidue m)

def PhiShiftedConstantResidues : Prop :=
  ∀ m : Nat, 0 < m → ∀ n : Nat, m - 100 ≤ n →
    Nat.ModEq m (Phi n) (fastControlResidue m)

def FastControlDoubleExponentResidueEnvelope : Prop :=
  ∀ m : Nat, 0 < m → ∀ s j : Nat, 1 ≤ s → 2 ≤ j → m ≤ 2 ^ (2 ^ s) →
    Nat.ModEq m (fastControl j s) (fastControlResidue m)

def PhiNextInputResidueEnvelope : Prop :=
  ∀ m : Nat, 0 < m → ∀ u : Nat, m ≤ 2 ^ (2 ^ Phi u) →
    Nat.ModEq m (Phi (u + 1)) (fastControlResidue m)

def FullFastControlConstantResidues : Prop :=
  FastControlResidueRange ∧ FastControlResiduePrimitiveRecursive ∧
    FastControlConstantResidues ∧ PhiShiftedConstantResidues ∧
    FastControlDoubleExponentResidueEnvelope ∧ PhiNextInputResidueEnvelope


end LogicLineages.StandardControlCurrent.GrowthResidueTargets
