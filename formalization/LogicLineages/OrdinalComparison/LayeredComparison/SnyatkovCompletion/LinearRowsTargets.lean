module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsTargets
open NormalForm LinearRows

def ActualRowArithmetic : Prop :=
  (∀ (z : Int) (ν : Nat → Nat), rowValue (rowConst z) ν = z) ∧
  (∀ (r s : Row) (ν : Nat → Nat), rowValue (rowAdd r s) ν = rowValue r ν + rowValue s ν) ∧
  (∀ (z : Int) (r : Row) (ν : Nat → Nat), rowValue (rowScale z r) ν = z * rowValue r ν)
def ActualLinearRowSplit : Prop := ∀ (i : Nat) (r : Row), rowLinear i r = true →
  ∀ (ν : Nat → Nat) (n : Nat),
    rowValue r (Function.update ν i n) = rowValue (remainder i r) ν + leading i r * (n : Int)
/-- Nonlinear occurrences at i are excluded even if their coefficient vanishes. -/
def ExactLinearityTest : Prop := ∀ (i : Nat) (p : Formula),
  isLinear i p = true ↔
    ∀ a ∈ atoms p, ∀ w ∈ a.row.2, w.2.name = i → w.2 = Summand.variable i
def PositiveCoefficientModulus : Prop := ∀ (i : Nat) (p : Formula), 0 < coefficientModulus i p
def PositiveUnitPeriod : Prop := ∀ u : UnitFormula, 0 < period u
def ActualNormalization : Prop := ∀ (i : Nat) (p : Formula), isLinear i p = true →
  ∀ ν : Nat → Nat,
    (∃ n : Nat, p.eval (Function.update ν i n)) ↔ ∃ n : Nat, unitEval (normalize i p) ν (n : Int)
/-- All symbolic remainders are evaluated under one fixed original valuation. -/
def ActualUnitElimination : Prop := ∀ (u : UnitFormula) (ν : Nat → Nat),
  (unitEliminate u).eval ν ↔ ∃ n : Nat, unitEval u ν (n : Int)
def ActualLinearElimination : Prop := ∀ (i : Nat) (p : Formula), isLinear i p = true →
  ∀ ν : Nat → Nat, (eliminate i p).eval ν ↔ ∃ n : Nat, p.eval (Function.update ν i n)
/-- Zero weights stay in symbolic rows, giving exact support rather than only containment. -/
def ExactOutputSupport : Prop := ∀ (i : Nat) (p : Formula) (v : Nat),
  v ∈ (eliminate i p).variables ↔ v ≠ i ∧ v ∈ p.variables
def ActualGuardedAtomElimination : Prop := ∀ (i : Nat) (a : Atom),
  isLinear i (guardedAtom a) = true → ∀ ν : Nat → Nat,
    (eliminate i (guardedAtom a)).eval ν ↔
      ∃ n : Nat, rowMeaningful a.row (Function.update ν i n) ∧ a.eval (Function.update ν i n)
def LiteralCodeCalibration : Prop :=
  (∀ (i : Nat) (p : Formula), Code.isLinear i p.encode = isLinear i p) ∧
  (∀ (i : Nat) (p : Formula), Code.normalize i p.encode = unitEncode (normalize i p)) ∧
  (∀ u : UnitFormula, Code.unitEliminate (unitEncode u) = (unitEliminate u).encode) ∧
  (∀ (i : Nat) (p : Formula), Code.eliminate i p.encode = (eliminate i p).encode)
def ActualNumericPrograms : Prop :=
  Primrec₂ Code.isLinear ∧ Primrec₂ Code.normalize ∧ Primrec Code.unitEliminate ∧ Primrec₂ Code.eliminate

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsTargets
