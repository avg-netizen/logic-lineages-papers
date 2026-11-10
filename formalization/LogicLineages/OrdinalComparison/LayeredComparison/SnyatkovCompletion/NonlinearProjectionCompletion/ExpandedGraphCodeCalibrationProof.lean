module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeAllocationCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeClauseCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
theorem graph_step (start n tag : Nat) (ht : tag < 10) :
    graph start (10 * n + tag) =
  if tag = 0 then SourceTermGraph.Code.equation (SourceTermGraph.Code.numeralRow start n)
  else if tag = 1 then SourceTermGraph.Code.equation (SourceTermGraph.Code.variableRow start n)
  else if tag = 2 then
    let a := n.unpair.1
    let b := n.unpair.2
    SourceTermGraph.Code.conjunction (graph start a)
      (SourceTermGraph.Code.conjunction (graph (start + nodeCount a) b)
        (SourceTermGraph.Code.equation (SourceTermGraph.Code.additionRow (output start (10 * n + tag))
          (output start a) (output (start + nodeCount a) b))))
  else if tag = 3 then
    let a := n.unpair.1
    let b := n.unpair.2
    SourceTermGraph.Code.conjunction (graph start a)
      (SourceTermGraph.Code.conjunction (graph (start + nodeCount a) b)
        (subtraction (output start (10 * n + tag)) (output start a) (output (start + nodeCount a) b)))
  else if tag = 4 then
    let a := n.unpair.2
    SourceTermGraph.Code.conjunction (graph start a)
      (SourceTermGraph.Code.equation (multiplyRow (output start (10 * n + tag)) (output start a) n.unpair.1))
  else if tag = 5 then
    let a := n.unpair.2
    SourceTermGraph.Code.conjunction (graph start a)
      (division (output start (10 * n + tag)) (output start a) n.unpair.1)
  else if tag = 6 then
    SourceTermGraph.Code.conjunction (graph start n)
      (SourceTermGraph.Code.equation (SourceTermGraph.Code.phiRow (output start (10 * n + tag)) (output start n)))
  else if tag = 8 then
    SourceTermGraph.Code.conjunction (graph start n)
      (inverse (start + nodeCount n) (output start (10 * n + tag)) (output start n))
  else 1
 := by
  have hm : (10 * n + tag) % 10 = tag := by omega
  have hd : (10 * n + tag) / 10 = n := by omega
  rw [graph, hm, hd]
#print axioms graph_step

theorem literalGraphCalibration : ExpandedGraphCodeTargets.LiteralGraphCalibration := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      simpa only [Term.encode, Nat.add_zero, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration] using graph_step start n 0 (by decide)
  | «variable» i =>
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration] using graph_step start i 1 (by decide)
  | add a b ha hb =>
      have ho : output start (10 * (Nat.pair a.encode b.encode) + 2) = ExpandedGraph.output start (Term.add a b) :=
        output_calibration start (Term.add a b)
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration, ho, ha, hb] using graph_step start (Nat.pair a.encode b.encode) 2 (by decide)
  | subtract a b ha hb =>
      have ho : output start (10 * (Nat.pair a.encode b.encode) + 3) = ExpandedGraph.output start (Term.subtract a b) :=
        output_calibration start (Term.subtract a b)
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration, ho, ha, hb] using graph_step start (Nat.pair a.encode b.encode) 3 (by decide)
  | multiply c a ha =>
      have ho : output start (10 * (Nat.pair c a.encode) + 4) = ExpandedGraph.output start (Term.multiply c a) :=
        output_calibration start (Term.multiply c a)
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration, ho, ha] using graph_step start (Nat.pair c a.encode) 4 (by decide)
  | divide c a ha =>
      have ho : output start (10 * (Nat.pair c a.encode) + 5) = ExpandedGraph.output start (Term.divide c a) :=
        output_calibration start (Term.divide c a)
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration, ho, ha] using graph_step start (Nat.pair c a.encode) 5 (by decide)
  | phi a ha =>
      have ho : output start (10 * a.encode + 6) = ExpandedGraph.output start (Term.phi a) :=
        output_calibration start (Term.phi a)
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration, ho, ha] using graph_step start a.encode 6 (by decide)
  | hyper a ha =>
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration] using graph_step start a.encode 7 (by decide)
  | phiInverse a ha =>
      have ho : output start (10 * a.encode + 8) = ExpandedGraph.output start (Term.phiInverse a) :=
        output_calibration start (Term.phiInverse a)
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration, ho, ha] using graph_step start a.encode 8 (by decide)
  | hyperInverse a ha =>
      simpa only [Term.encode, ExpandedGraph.graph, NormalForm.Formula.encode,
        SourceTermGraph.Code.conjunction, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
        nodeCount_calibration, output_calibration, equation_numeral_calibration,
        equation_variable_calibration, equation_addition_calibration, equation_phi_calibration,
        equation_multiply_calibration, subtraction_calibration, division_calibration,
        inverse_calibration] using graph_step start a.encode 9 (by decide)
#print axioms literalGraphCalibration


end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
