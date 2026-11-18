module
public import LogicLineages.StandardControlCurrent.RankedRowDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.RankedRowTargets
open OrdinalComparison PolynomialGraphCompletion RankedWordDecisionCompletion Runner

def RowCalibration : Prop := ∀ D r, RowAllowed D r → ∀ ν,
  (RankedRow.RowDomain r ν ↔ PolynomialGraphCompletion.RowDomain r ν) ∧
  (RankedRow.RowDomain r ν → RankedRow.RowValue r ν = PolynomialGraphCompletion.RowValue r ν)

def AllInputTermination : Prop := ∀ D maximum r,
  ∃ fuel : Nat, stopped D maximum r fuel = true

def ExactLeastStopping : Prop := ∀ D maximum r,
  stopped D maximum r (leastFuel D maximum r) = true ∧
  (∀ n, n < leastFuel D maximum r → stopped D maximum r n = false) ∧
  (admitted D r = false → leastFuel D maximum r = 0)

def FiniteRunnerProgram : Prop :=
  Computable (fun input : Nat × Nat × Row × Nat =>
    encodeState (run input.1 input.2.1 input.2.2.1 input.2.2.2))

def LeastFuelProgram : Prop :=
  Computable (fun input : Nat × Nat × Row =>
    leastFuel input.1 input.2.1 input.2.2)

def ExactSingleRowPackage : Prop := ∀ D maximum r, 3 ≤ D → RowAllowed D r →
  RankedRow.PackageCorrect D maximum [r] (solve D maximum r)

def ExactFamilyPackage : Prop := ∀ D maximum rows,
  3 ≤ D → (∀ r ∈ rows, RowAllowed D r) →
    RankedRow.PackageCorrect D maximum rows (compile D maximum rows)

def ActualFamilyProgram : Prop :=
  Computable (fun input : Nat × Nat × List Row =>
    encodePackage (compile input.1 input.2.1 input.2.2))


def Full : Prop := RowCalibration ∧ AllInputTermination ∧ ExactLeastStopping ∧
  FiniteRunnerProgram ∧ LeastFuelProgram ∧ ExactSingleRowPackage ∧ ExactFamilyPackage ∧ ActualFamilyProgram
end LogicLineages.StandardControlCurrent.RankedRowTargets
