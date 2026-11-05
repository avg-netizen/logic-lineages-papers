module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsTargets
open NormalForm HyperBranchRows

def ActualGuardCalibration : Prop := ∀ (i j : Nat) (e h k l : Int) (c : Nat) (ν : Nat → Nat),
  (closeGuard i j e h k l c).eval ν ↔ (HyperWindow.closeMatrix i j e h k l c).eval ν
/-- Each restricted-row output agrees with the already accepted expanded
source branch at every valuation, including the entire equal-index case. -/
def ActualBranchCalibration : Prop := ∀ (i j : Nat) (e h k l : Int) (c : Nat)
    (p : Formula) (ν : Nat → Nat),
  ((leftCases i j e h k l c p).eval ν ↔ (HyperWindow.leftCases i j e h k l c p.compile).eval ν) ∧
  ((rightCases i j e h k l c p).eval ν ↔ (HyperWindow.rightCases i j e h k l c p.compile).eval ν) ∧
  ((equalCases i j e h k l c p).eval ν ↔ (HyperWindow.equalCases i j e h k l c p.compile).eval ν)
/-- The full source II6 clause decreases two original existential names to
one in every branch, with unrestricted correlated Boolean row bodies. -/
def ActualTwoVariableElimination : Prop := ∀ (i j : Nat), i ≠ j →
  ∀ (e h k l : Int) (c : Nat) (p : Formula) (ν : Nat → Nat),
    (∃ x y : Nat, (HyperWindow.closeMatrix i j e h k l c).eval
      (Function.update (Function.update ν i x) j y) ∧
      p.eval (Function.update (Function.update ν i x) j y)) ↔
    (∃ y : Nat, (leftCases i j e h k l c p).eval (Function.update ν j y)) ∨
    (∃ x : Nat, (rightCases i j e h k l c p).eval (Function.update ν i x)) ∨
    (∃ y : Nat, (equalCases i j e h k l c p).eval (Function.update ν j y))
def ExactBranchSupport : Prop := ∀ (i j : Nat), i ≠ j →
  ∀ (e h k l : Int) (c : Nat) (p : Formula) (v : Nat),
    (v ∈ (leftCases i j e h k l c p).variables ↔ v ≠ i ∧ (v = j ∨ v ∈ p.variables)) ∧
    (v ∈ (rightCases i j e h k l c p).variables ↔ v ≠ j ∧ (v = i ∨ v ∈ p.variables)) ∧
    (v ∈ (equalCases i j e h k l c p).variables ↔ v ≠ i ∧ (v = j ∨ v ∈ p.variables))
def LiteralBranchCodeCalibration : Prop := ∀ (i j : Nat) (e h k l : Int) (c : Nat) (p : Formula),
  Code.leftCases (HyperWindowCode.input i j e h k l c p.encode) =
    (leftCases i j e h k l c p).encode ∧
  Code.rightCases (HyperWindowCode.input i j e h k l c p.encode) =
    (rightCases i j e h k l c p).encode ∧
  Code.equalCases (HyperWindowCode.input i j e h k l c p.encode) =
    (equalCases i j e h k l c p).encode
def ActualBranchNumericPrograms : Prop :=
  Primrec Code.leftCases ∧ Primrec Code.rightCases ∧ Primrec Code.equalCases

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsTargets
