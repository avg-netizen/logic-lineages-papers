module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixTargets
import LogicLineages.PermittedControl.SharedRankResidueRowStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrix
open PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open SharedRankResidueRow (SourceRow Layout requests commonLayout)
open StatementChecks (fixed_sharedRankResidueFormulaSupport)

private theorem supported (layout : Layout) (rows : List SourceRow) :
    PlainPreparedFormula (formulaAtLayout layout rows) ∧
      ∀ i ∈ (formulaAtLayout layout rows).variables, i ∈ (requests layout).map Prod.fst := by
  induction rows with
  | nil => simp [formulaAtLayout,PlainPreparedFormula,LinearRows.atoms,NormalForm.Formula.variables]
  | cons r rest ih =>
    have head := fixed_sharedRankResidueFormulaSupport layout r
    constructor
    · intro a atom s summand
      rcases List.mem_append.mp atom with fromHead | fromRest
      · exact head.1 a fromHead s summand
      · exact ih.1 a fromRest s summand
    · intro i used
      rcases List.mem_append.mp used with fromHead | fromRest
      · exact head.2 i fromHead
      · exact ih.2 i fromRest

theorem formulaSupport : FormulaSupport := fun rows => supported (commonLayout rows) rows

end LogicLineages.PermittedControl.SignedCongruenceMatrix
