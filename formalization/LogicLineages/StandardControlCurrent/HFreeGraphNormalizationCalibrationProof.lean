module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationRawTraversalProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeCalibrationProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open HFreeGraphNormalization

theorem predicate_calibration (start : Nat) (p : Matrix) :
    Code.predicate start p.encode = (ExpandedBooleanGraph.predicate start p).encode := by
  induction p generalizing start with
  | truth => simpa [Matrix.encode, ExpandedBooleanGraph.predicate, NormalForm.Formula.encode] using predicate_step start 0 0 (by decide)
  | falsity => simpa [Matrix.encode, ExpandedBooleanGraph.predicate, NormalForm.Formula.encode] using predicate_step start 0 1 (by decide)
  | equal a b =>
      simpa [Matrix.encode, ExpandedBooleanGraph.predicate, Nat.unpair_pair,
        ExpandedGraphCodeProof.nodeCount_calibration, ExpandedGraphCodeProof.output_calibration,
        SourceRowsCodeProof.relation_calibration] using predicate_step start (Nat.pair a.encode b.encode) 2 (by decide)
  | less a b =>
      simpa [Matrix.encode, ExpandedBooleanGraph.predicate, Nat.unpair_pair,
        ExpandedGraphCodeProof.nodeCount_calibration, ExpandedGraphCodeProof.output_calibration,
        SourceRowsCodeProof.relation_calibration] using predicate_step start (Nat.pair a.encode b.encode) 3 (by decide)
  | divisible m a =>
      have he := SourceTermGraphCodeProof.equation_calibration
        (0, [(1, .variable (ExpandedGraph.output start a))])
      by_cases hm : m = 0
      · subst m
        have hs := predicate_step start (Nat.pair 0 a.encode) 4 (by decide)
        simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
          ExpandedGraphCodeProof.output_calibration] at hs
        exact hs.trans (by simpa [Matrix.encode, ExpandedBooleanGraph.predicate,
          ExpandedGraph.equation, NormalForm.rowData, NormalForm.Summand.data,
          SourceTermGraph.Code.variableData] using he)
      · simpa [Matrix.encode, ExpandedBooleanGraph.predicate, Nat.unpair_pair, hm,
          ExpandedGraphCodeProof.output_calibration, NormalForm.Formula.encode,
          NormalForm.Atom.data, NormalForm.rowData, NormalForm.Summand.data,
          SourceTermGraph.Code.variableData] using predicate_step start (Nat.pair m a.encode) 4 (by decide)
  | negative p ih =>
      simpa [Matrix.encode, ExpandedBooleanGraph.predicate, NormalForm.Formula.encode, ih] using
        predicate_step start p.encode 5 (by decide)
  | conjunction p q hp hq =>
      simpa [Matrix.encode, ExpandedBooleanGraph.predicate, NormalForm.Formula.encode,
        Nat.unpair_pair, hp, hq, forest_calibration, ExpandedGraphCodeProof.nodeCount_calibration] using
        predicate_step start (Nat.pair p.encode q.encode) 6 (by decide)
  | disjunction p q hp hq =>
      simpa [Matrix.encode, ExpandedBooleanGraph.predicate, NormalForm.Formula.encode,
        Nat.unpair_pair, hp, hq, forest_calibration, ExpandedGraphCodeProof.nodeCount_calibration] using
        predicate_step start (Nat.pair p.encode q.encode) 7 (by decide)

theorem names_calibration (i : Nat) (p : Matrix) :
    Code.names i p.encode = OriginalSourceElimination.graphNames i p := by
  unfold Code.names Code.startFor OriginalSourceElimination.graphNames ExpandedBooleanGraph.allocated ExpandedBooleanGraph.startFor
  rw [matrixVariables_calibration, forest_calibration]
  exact (ExpandedGraphCodeProof.literalAllocation _ _).1

theorem graphFormula_calibration (i : Nat) (p : Matrix) :
    Code.graphFormula i p.encode = (OriginalSourceElimination.graphFormula i p).encode := by
  unfold Code.graphFormula Code.startFor OriginalSourceElimination.graphFormula ExpandedBooleanGraph.compile ExpandedBooleanGraph.matrix ExpandedBooleanGraph.startFor
  rw [matrixVariables_calibration, forest_calibration, ExpandedGraphCodeProof.literalGraphCalibration, predicate_calibration]
  rfl

theorem literalCode : HFreeGraphNormalizationTargets.LiteralCode := by
  refine ⟨termVariables_calibration, (fun p => ⟨matrixVariables_calibration p,forest_calibration p⟩), predicate_calibration, ?_⟩
  intro i p
  refine ⟨names_calibration i p,graphFormula_calibration i p,?_⟩
  unfold Code.program Code.bound
  rw [names_calibration, graphFormula_calibration, WholeBoundInitializationCodeProof.literalFormulaCalibration]
  rfl
end LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
