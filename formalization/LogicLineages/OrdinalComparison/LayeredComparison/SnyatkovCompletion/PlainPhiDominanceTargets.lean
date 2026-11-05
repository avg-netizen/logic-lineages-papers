module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceTargets
open NormalForm PlainPhiDominance

/-- An explicit uniform bound from the actual Phi hierarchy. -/
def ActualGap : Prop := ∀ S A B n : Nat,
  S + A + B + 1 ≤ n → S * Phi (n - 1) + A * n + B < Phi n

/-- Correlated equal-argument cancellation preserves the original row exactly,
with the original occurrence mass controlling every surviving coefficient. -/
def ExactCollectedEvaluation : Prop := ∀ r : Row, isPlain r = true → ∀ ν : Nat → Nat,
  rowValue r ν = linearPart r ν +
    CommonHeadCollectedRow.weighted (fun n => (Phi n : Int))
      (CommonHeadCollectedRow.collect (phiData r ν)) ∧
  CommonHeadLargeRow.mass (CommonHeadCollectedRow.collect (phiData r ν)) ≤ mass r

def ActualCancelledRow : Prop := ∀ r : Row, isPlain r = true → ∀ ν : Nat → Nat,
  CommonHeadCollectedRow.collect (phiData r ν) = [] → rowValue r ν = linearPart r ν

/-- The source-shaped dominant boundary. Original names retain one common
valuation. A maximal raw name must still own a surviving nonlinear block;
no conclusion is drawn merely from a cancelled occurrence at that name. -/
def ActualMaximalRawDominance : Prop := ∀ (r : Row), isPlain r = true →
  ∀ (i : Nat) (ν : Nat → Nat), threshold r ≤ ν i →
    (∀ a ∈ r.2, ν a.2.name ≤ ν i) → active i r ν = true →
    ∀ leader ∈ CommonHeadCollectedRow.collect (phiData r ν),
      (∀ a ∈ CommonHeadCollectedRow.collect (phiData r ν), a.2 ≤ leader.2) →
      Int.sign (rowValue r ν) = Int.sign leader.1

def LiteralThresholdCalibration : Prop := ∀ r : Row,
  Code.isPlain (rowData r) = isPlain r ∧ Code.mass (rowData r) = mass r ∧
    Code.shiftMass (rowData r) = shiftMass r ∧ Code.threshold (rowData r) = threshold r

def ActualThresholdPrograms : Prop :=
  Primrec Code.isPlain ∧ Primrec Code.mass ∧ Primrec Code.shiftMass ∧ Primrec Code.threshold

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceTargets
