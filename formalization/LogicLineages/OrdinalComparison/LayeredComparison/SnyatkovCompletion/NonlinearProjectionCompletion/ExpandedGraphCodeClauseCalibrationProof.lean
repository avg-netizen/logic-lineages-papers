module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeCalibrationProof
public import Mathlib.Tactic.SplitIfs
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
theorem multiplyRow_calibration (z x c : Nat) :
    multiplyRow z x c = NormalForm.rowData (ExpandedGraph.multiplyRow z x c) := rfl
#print axioms multiplyRow_calibration

theorem subtraction_calibration (z x y : Nat) :
    subtraction z x y = (ExpandedGraph.subtraction z x y).encode := rfl
#print axioms subtraction_calibration

theorem division_calibration (z x c : Nat) :
    division z x c = (ExpandedGraph.division z x c).encode := by
  unfold division ExpandedGraph.division
  split_ifs <;> rfl
#print axioms division_calibration

theorem inverse_calibration (u z x : Nat) :
    inverse u z x = (ExpandedGraph.inverse u z x).encode := rfl
#print axioms inverse_calibration

theorem literalLocalClauses : ExpandedGraphCodeTargets.LiteralLocalClauses :=
  ⟨multiplyRow_calibration, subtraction_calibration, division_calibration, inverse_calibration⟩
#print axioms literalLocalClauses

theorem equation_numeral_calibration (z n : Nat) :
    SourceTermGraph.Code.equation (SourceTermGraph.Code.numeralRow z n) = (ExpandedGraph.equation (SourceTermGraph.numeralRow z n)).encode :=
  SourceTermGraphCodeProof.equation_calibration (SourceTermGraph.numeralRow z n)
#print axioms equation_numeral_calibration

theorem equation_variable_calibration (z i : Nat) :
    SourceTermGraph.Code.equation (SourceTermGraph.Code.variableRow z i) = (ExpandedGraph.equation (SourceTermGraph.variableRow z i)).encode :=
  SourceTermGraphCodeProof.equation_calibration (SourceTermGraph.variableRow z i)
#print axioms equation_variable_calibration

theorem equation_addition_calibration (z x y : Nat) :
    SourceTermGraph.Code.equation (SourceTermGraph.Code.additionRow z x y) = (ExpandedGraph.equation (SourceTermGraph.additionRow z x y)).encode :=
  SourceTermGraphCodeProof.equation_calibration (SourceTermGraph.additionRow z x y)
#print axioms equation_addition_calibration

theorem equation_phi_calibration (z x : Nat) :
    SourceTermGraph.Code.equation (SourceTermGraph.Code.phiRow z x) = (ExpandedGraph.equation (SourceTermGraph.phiRow z x)).encode :=
  SourceTermGraphCodeProof.equation_calibration (SourceTermGraph.phiRow z x)
#print axioms equation_phi_calibration

theorem equation_multiply_calibration (z x c : Nat) :
    SourceTermGraph.Code.equation (multiplyRow z x c) = (ExpandedGraph.equation (ExpandedGraph.multiplyRow z x c)).encode :=
  SourceTermGraphCodeProof.equation_calibration (ExpandedGraph.multiplyRow z x c)
#print axioms equation_multiply_calibration


-- Explicit audits of the unchanged freshly compiled public supplier declarations.
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.instructions_calibration
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.instructions_length
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.instructionCodeCalibration
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.numeralRow_data
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.variableRow_data
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.additionRow_data
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.phiRow_data
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.run_append
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.rowMachineCalibration
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.negateRow_data
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.equation_calibration
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.equations_calibration
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.literalGraphCompiler

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
