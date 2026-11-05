module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationTargets
open NormalForm ZeroValuation

def ActualRowProjection : Prop := ∀ (r : Row) (ν : Nat → Nat),
  rowValue (projectRow r) ν = rowValue r (fun _ => 0)

def ExactConstantProjection : Prop := ∀ p : Formula, (project p).variables = []

def ActualProjection : Prop := ∀ (p : Formula) (ν : Nat → Nat),
  (project p).eval ν ↔ p.eval (fun _ => 0)

def ActualZeroEvaluator : Prop := ∀ p : Formula, evaluate p = true ↔ p.eval (fun _ => 0)

def LiteralCodeCalibration : Prop :=
  (∀ r : Row, Code.projectRow (rowData r) = rowData (projectRow r)) ∧
  (∀ a : Atom, Code.projectAtom a.data = (projectAtom a).data) ∧
  (∀ p : Formula, Code.project p.encode = (project p).encode) ∧
  (∀ p : Formula, Code.evaluate p.encode = evaluate p)

def ActualNumericPrograms : Prop :=
  Primrec Code.projectRow ∧ Primrec Code.projectAtom ∧ Primrec Code.project ∧ Primrec Code.evaluate

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationTargets
