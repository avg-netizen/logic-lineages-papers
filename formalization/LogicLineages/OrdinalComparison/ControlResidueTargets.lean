module
public import LogicLineages.OrdinalComparison.ControlResidueDefinitions
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Data.Nat.ModEq

@[expose] public section

/-! Independent paper08 lem:growth and lem:residues source targets, also fixing
the three uniform envelopes of paper10 thm:envelope. The control remains the
literal variable-seed hierarchy. The witness is a fixed numerical function,
with genuine primitive recursion required; no CRT/residue oracle is a premise. -/

namespace LogicLineages.OrdinalComparison.Targets

def FullFastControlHierarchyGrowth : Prop :=
  (∀ j : Nat, Computable (fastControl j) ∧ StrictMono (fastControl j) ∧
    ∀ n : Nat, 2 ^ n ≤ fastControl j n) ∧
  (∀ j n : Nat, 2 ^ (fastControl (j + 1) n + 1) ≤ fastControl (j + 1) (n + 1)) ∧
  (∀ A z : Nat, A ≤ z → (A + 2) * Phi z ≤ Phi (z + 1))

def ExponentTowerResidueStability : Prop :=
  ∀ m : Nat, 0 < m → ∀ n n' k k' : Nat,
    m ≤ n → m ≤ n' → m ≤ k → m ≤ k' →
    Nat.ModEq m ((fastControl 0)^[k] n) ((fastControl 0)^[k'] n')

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

def FullUniformResidueEnvelopes : Prop :=
  FastControlResidueRange ∧ FastControlResiduePrimitiveRecursive ∧
    (∀ m : Nat, 0 < m → ∀ x : Nat, m ≤ x → Nat.ModEq m (Phi x) (fastControlResidue m)) ∧
    FastControlDoubleExponentResidueEnvelope ∧ PhiNextInputResidueEnvelope

end LogicLineages.OrdinalComparison.Targets
