module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeTargets
open PlainBlockDispatchCode

/-- Exact original name-only occurrence renaming, with tied parameter terms
unchanged. No parameter-independence premise is needed for syntax calibration. -/
def LiteralRenameCalibration : Prop :=
  (∀ (i j : Nat) (s : NormalForm.Summand),
    renameItem i j s.data = (PlainBlockSplit.renameSummand i j s).data) ∧
  (∀ (i j : Nat) (r : BlockRows.Row),
    renameRow i j (BlockRowSubstitutionCode.rowData r) =
      BlockRowSubstitutionCode.rowData (PlainBlockSplit.renameRow i j r)) ∧
  (∀ (i j : Nat) (p : BlockRows.Formula),
    rename i j (BlockFormulaSubstitutionCode.formulaCode p) =
      BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.rename i j p))

/-- Every original small/tie/band/far branch, in the original list order,
for arbitrary bounds and formulas, not merely well-formed reachable states. -/
def LiteralBranchFamiliesCalibration : Prop := ∀ (bound : List Nat) (p : BlockRows.Formula),
  small bound (BlockFormulaSubstitutionCode.formulaCode p) =
    (PlainBlockSplit.small bound p).map stateData ∧
  ties bound (BlockFormulaSubstitutionCode.formulaCode p) =
    (PlainBlockSplit.ties bound p).map stateData ∧
  bands bound (BlockFormulaSubstitutionCode.formulaCode p) =
    (PlainBlockSplit.bands bound p).map stateData ∧
  far bound (BlockFormulaSubstitutionCode.formulaCode p) =
    (PlainBlockSplit.far bound p).map stateData

def LiteralBranchAssemblyCalibration : Prop := ∀ (bound : List Nat) (p : BlockRows.Formula),
  branches bound (BlockFormulaSubstitutionCode.formulaCode p) =
    (PlainBlockSplit.branches bound p).map stateData

def LiteralAdvanceCalibration : Prop := ∀ states : List PlainBlockSplit.State,
  advance (states.map stateData) = (PlainBlockSplit.advance states).map stateData

/-- The same finite iteration, at arbitrary runtime fuel and state lists.
No decrease, allowedness, Nodup, origin or effectiveness premise is supplied. -/
def LiteralRunCalibration : Prop := ∀ (fuel : Nat) (states : List PlainBlockSplit.State),
  run fuel (states.map stateData) = (PlainBlockSplit.run fuel states).map stateData

def ActualDispatchPrograms : Prop :=
  Computable (fun p : Nat × (Nat × NormalForm.Code.ItemData) => renameItem p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × (Nat × RowData) => renameRow p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × (Nat × Nat) => rename p.1 p.2.1 p.2.2) ∧
  Computable₂ small ∧ Computable₂ ties ∧ Computable₂ bands ∧ Computable₂ far ∧
  Computable₂ branches ∧ Computable advance ∧ Computable₂ run

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeTargets
