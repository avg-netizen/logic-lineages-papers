module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearTargets
open NormalForm SourceRows

def ExactConstantMatrixTest : Prop := ∀ p : Formula,
  ClosedLinear.constantMatrix p = true ↔ p.variables = []

def ActualConstantEvaluator : Prop := ∀ p : Formula,
  ClosedLinear.constantMatrix p = true → ∀ ν : Nat → Nat,
    ClosedLinear.evaluateConstants p = true ↔ p.eval ν

def ExactDecisionDomain : Prop := ∀ p : QFormula,
  (ClosedLinear.decideClosed p).isSome =
    (QuantifiedLinear.admissible p && p.variables.isEmpty)

def ActualClosedDecision : Prop := ∀ p : QFormula,
  QuantifiedLinear.admissible p = true → p.variables = [] →
    ∀ (ν : Nat → Nat) (answer : Bool),
      ClosedLinear.decideClosed p = some answer ↔ (p.eval ν ↔ answer = true)

def LiteralCodeCalibration : Prop :=
  (∀ p : Formula, ClosedLinear.Code.constantMatrix p.encode = ClosedLinear.constantMatrix p) ∧
  (∀ p : Formula, ClosedLinear.Code.evaluateConstants p.encode = ClosedLinear.evaluateConstants p) ∧
  (∀ p : QFormula, ClosedLinear.Code.decideClosed p.encode = ClosedLinear.decideClosed p)

def ActualNumericPrograms : Prop :=
  Primrec ClosedLinear.Code.constantMatrix ∧ Primrec ClosedLinear.Code.evaluateConstants ∧
    Primrec ClosedLinear.Code.decideClosed

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearTargets
