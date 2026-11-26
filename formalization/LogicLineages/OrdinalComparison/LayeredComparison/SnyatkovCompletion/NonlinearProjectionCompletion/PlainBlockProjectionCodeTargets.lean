module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeTargets
open PlainBlockProjectionCode

/-- Syntax calibration on complete original rows, with no allowedness or
parameter-independence restriction. -/
def LiteralTermCalibration : Prop := ∀ r : BlockRows.Row,
  positiveTerm (BlockRowSubstitutionCode.rowData r) = (BlockRows.positiveTerm r).encode ∧
  negativeTerm (BlockRowSubstitutionCode.rowData r) = (BlockRows.negativeTerm r).encode ∧
  absoluteTerm (BlockRowSubstitutionCode.rowData r) = (BlockRows.absoluteTerm r).encode

def LiteralAtomCalibration : Prop := ∀ a : BlockRows.Atom,
  atom (BlockFormulaSubstitutionCode.atomData a) = a.compile.encode

def LiteralFormulaCompilation : Prop := ∀ p : BlockRows.Formula,
  formula (BlockFormulaSubstitutionCode.formulaCode p) = p.compile.encode

/-- Read the exact original state list in order, including arbitrary residual
bounds and duplicate states, without assuming completion or reachability. -/
def LiteralReadoutCalibration : Prop := ∀ states : List PlainBlockSplit.State,
  readout (states.map PlainBlockDispatchCode.stateData) =
    (Matrix.any (states.map (fun s => s.2.compile))).encode

/-- Literal original projector code, not an unconditional semantic QE claim.
The existing semantic projection theorem keeps its original hypotheses. -/
def LiteralProjectorCalibration : Prop := ∀ (bound : List Nat) (p : BlockRows.Formula),
  project bound (BlockFormulaSubstitutionCode.formulaCode p) =
    (PlainBlockSplit.project bound p).encode

/-- All actual programs are closed and joint in their runtime inputs. -/
def ActualProjectionPrograms : Prop :=
  Computable positiveTerm ∧ Computable negativeTerm ∧ Computable absoluteTerm ∧
  Computable atom ∧ Computable formula ∧ Computable readout ∧ Computable₂ project

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeTargets
