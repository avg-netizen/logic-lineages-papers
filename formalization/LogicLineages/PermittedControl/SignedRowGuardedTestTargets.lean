module
public import LogicLineages.PermittedControl.SignedRowSliceValueTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowGuardedTest
open MixedSameRankResidue (WeightedOperand)
open SignedRowCoordinateSlice (slice firstFailure)
open SignedRowSliceValue (valueAt)

inductive Test where
  | equalZero
  | nonnegative
  | positive
  | congruence (modulus : Nat)

def Test.Admitted : Test → Prop
  | .congruence m => 0 < m
  | _ => True

def Test.Holds : Test → Int → Prop
  | .equalZero, v => v = 0
  | .nonnegative, v => 0 ≤ v
  | .positive, v => 0 < v
  | .congruence m, v => (m : Int) ∣ v

def Test.atPolarity (test : Test) (positive : Bool) (value : Int) : Prop :=
  if positive then test.Holds value else ¬ test.Holds value

def residualValueAt (f ρ : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand)
    (value : Int) : Prop :=
  ∃ (b : Int) (residual : List WeightedOperand),
    slice f rank a c terms = some (some (b,residual)) ∧ valueAt f ρ b residual value

def sourceTestAt (f ρ : Nat → Nat) (c : Int) (terms : List WeightedOperand)
    (test : Test) (positive : Bool) : Prop :=
  test.Admitted ∧ ∃ value : Int, valueAt f ρ c terms value ∧ test.atPolarity positive value

def residualTestAt (f ρ : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand)
    (test : Test) (positive : Bool) : Prop :=
  test.Admitted ∧ ∃ value : Int, residualValueAt f ρ rank a c terms value ∧ test.atPolarity positive value

def ExactValue : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand),
    ρ rank = a → ∀ value : Int,
      valueAt f ρ c terms value ↔ residualValueAt f ρ rank a c terms value

def ExactSelectedFailures : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand),
    ρ rank = a →
    (slice f rank a c terms = none →
      firstFailure f rank a terms .invalid ∧ ∀ value : Int, ¬ valueAt f ρ c terms value) ∧
    (slice f rank a c terms = some none →
      firstFailure f rank a terms .genuineMiss ∧ ∀ value : Int, ¬ valueAt f ρ c terms value)

def ExactGuardedTests : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand),
    ρ rank = a → ∀ (test : Test) (positive : Bool),
      (sourceTestAt f ρ c terms test positive ↔ residualTestAt f ρ rank a c terms test positive)

def ZeroModulusExcluded : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand) (positive : Bool),
    ¬ sourceTestAt f ρ c terms (.congruence 0) positive ∧
    ¬ residualTestAt f ρ rank a c terms (.congruence 0) positive

def FullSignedRowGuardedTest : Prop :=
  ExactValue ∧ ExactSelectedFailures ∧ ExactGuardedTests ∧ ZeroModulusExcluded

end LogicLineages.PermittedControl.SignedRowGuardedTest
