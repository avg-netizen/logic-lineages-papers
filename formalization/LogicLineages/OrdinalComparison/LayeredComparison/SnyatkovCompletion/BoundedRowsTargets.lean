module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsTargets
open NormalForm BoundedRows

def ActualRowSubstitution : Prop := ∀ (i n : Nat) (row : Row) (ν : Nat → Nat),
  rowValue (rowSubstitute i n row) ν = rowValue row (Function.update ν i n)
def ExactResidualOccurrences : Prop := ∀ (i n : Nat) (row : Row),
  (rowSubstitute i n row).2 = row.2.filter (fun a => a.2.name != i)
def ExactOriginalDomains : Prop := ∀ (i n : Nat) (row : Row) (ν : Nat → Nat),
  rowMeaningful row (Function.update ν i n) ↔
    fixedCutoff i row ≤ n ∧ rowMeaningful (rowSubstitute i n row) ν
def ActualFormulaSubstitution : Prop := ∀ (i n : Nat) (p : Formula) (ν : Nat → Nat),
  (substitute i n p).eval ν ↔ p.eval (Function.update ν i n)
def ExactSubstitutionSupport : Prop := ∀ (i n : Nat) (p : Formula) (v : Nat),
  v ∈ (substitute i n p).variables ↔ v ≠ i ∧ v ∈ p.variables
def ActualBoundedElimination : Prop := ∀ (i bound : Nat) (p : Formula) (ν : Nat → Nat),
  (bounded i bound p).eval ν ↔ ∃ n : Nat, n < bound ∧ p.eval (Function.update ν i n)
def ExactBoundedSupport : Prop := ∀ (i bound : Nat) (p : Formula) (v : Nat),
  v ∈ (bounded i bound p).variables ↔ 0 < bound ∧ v ≠ i ∧ v ∈ p.variables
def ActualBlockElimination : Prop := ∀ (bounds : List (Nat × Nat)) (p : Formula) (ν : Nat → Nat),
  (block bounds p).eval ν ↔ boundedPrefix ν bounds p
def ExactBlockSupport : Prop := ∀ (bounds : List (Nat × Nat)) (p : Formula) (v : Nat),
  v ∈ (block bounds p).variables ↔
    (∀ entry ∈ bounds, 0 < entry.2) ∧ v ∉ bounds.map Prod.fst ∧ v ∈ p.variables
/-- The original source prefix uses the final valuation for all bound rows;
distinct binder names make it exactly the separately bounded construction. -/
def ExactExistingPrefix : Prop := ∀ (bounds : List (Nat × Nat)),
  (bounds.map Prod.fst).Nodup → ∀ (p : Formula) (ν : Nat → Nat),
    (block bounds p).eval ν ↔
      existsPrefix ν (bounds.map Prod.fst) (.conjunction (boundsFormula bounds) p)
def LiteralCodeCalibration : Prop :=
  (∀ (s : Summand) (n : Nat), Code.itemValue s.data n = valueAt s n) ∧
  (∀ (i n : Nat) (row : Row), Code.row i n (rowData row) = rowData (rowSubstitute i n row) ∧
    Code.fixedCutoff i (rowData row) = fixedCutoff i row) ∧
  (∀ (i n : Nat) (p : Formula), Code.formula i n p.encode = (substitute i n p).encode) ∧
  (∀ (i bound : Nat) (p : Formula), Code.bounded i bound p.encode = (bounded i bound p).encode) ∧
  (∀ (bounds : List (Nat × Nat)) (p : Formula), Code.block bounds p.encode = (block bounds p).encode)
def ActualNumericPrograms : Prop :=
  Primrec₂ Code.itemValue ∧
  Primrec₂ (fun args : Nat × Nat => Code.row args.1 args.2) ∧
  Primrec₂ Code.fixedCutoff ∧
  Primrec₂ (fun args : Nat × Nat => Code.formula args.1 args.2) ∧
  Primrec₂ (fun args : Nat × Nat => Code.bounded args.1 args.2) ∧ Primrec₂ Code.block

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsTargets
