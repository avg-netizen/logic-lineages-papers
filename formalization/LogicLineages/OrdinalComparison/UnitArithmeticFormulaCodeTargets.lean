module
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode.Targets
open Arithmetic ArithmeticCode OriginalDomain

def ExactTreeExpansion : Prop := ∀ (Γ : List Ty) (q : UnitElimination.Tree Nat Γ)
    (xs : List Expr) (r : Expr),
  unitFormulaCode (UnitEliminationTreeCode.code q) (xs.map exprCode) (exprCode r) =
    formulaCode (unitFormula q xs r)

def EffectiveAlgorithms : Prop :=
  Primrec (fun p : Nat×List Nat×Nat => unitFormulaCode p.1 p.2.1 p.2.2) ∧
  Computable (fun p : List Nat×Nat×List Nat×Nat => sourceFormulaCode p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Every actual typed source, with a covering ordered shared input tuple,
compiles successfully to literal source arithmetic for its actual scalar. -/
def ActualSourceFormula : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ)
    (xs : List Expr) (r : Expr), Γ.length ≤ xs.length →
  ∃ f : Formula,
    sourceFormulaCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t)
      (xs.map exprCode) (exprCode r) = some (formulaCode f) ∧
    ∀ ν : Nat → Nat, f.eval ν ↔
      ∃ v : OrdinalVector Γ τ.level,
        AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v ∧
        expressionValue (UnitObservation.substitution (inputValues ν xs)) (v 0) = (r.value ν : Ordinal)
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode.Targets
