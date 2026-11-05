module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsShiftProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphDecisionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
open NormalForm CommonLayerSyntax SourceBooleanPrograms

theorem count_calibration (t : BaseTerm) : Code.count t.encode = SourceTermGraph.nodeCount t := by
  rw [Code.count, SourceTermGraphCodeProof.instructions_calibration, SourceTermGraphCodeProof.instructions_length]

private theorem payload_step (a tag : Nat) (ht : tag < 5) :
    Code.payload (5 * a + tag) =
      if tag = 0 ∨ tag = 1 then
        (true, 4 * Nat.pair a.unpair.1 a.unpair.2 + 2,
          SourceRows.Code.relation (tag == 1) (Code.count a.unpair.1 - 1)
            (Code.count a.unpair.1 + Code.count a.unpair.2 - 1))
      else if tag = 2 then
        ((Code.payload a).1, (Code.payload a).2.1, 6 * (Code.payload a).2.2 + 3)
      else if tag = 3 then
        ((Code.payload a.unpair.1).1 && (Code.payload a.unpair.2).1,
          4 * Nat.pair (Code.payload a.unpair.1).2.1 (Code.payload a.unpair.2).2.1 + 2,
          6 * Nat.pair (Code.payload a.unpair.1).2.2
            (Code.shift (Code.count (Code.payload a.unpair.1).2.1) (Code.payload a.unpair.2).2.2) + 4)
      else (false, (Code.payload a.unpair.2).2.1, 1) := by
  have hm : (5 * a + tag) % 5 = tag := by omega
  have hd : (5 * a + tag) / 5 = a := by omega
  rw [Code.payload, hm, hd]

theorem literalPayload : SourceBooleanProgramsTargets.LiteralPayload := by
  intro p
  induction p with
  | equal a b =>
      simpa [SourceFormula.encode, SourceBooleanGraph.test, SourceBooleanGraph.forest,
        SourceBooleanGraph.predicate, BaseTerm.encode, Nat.unpair_pair, count_calibration,
        SourceRowsCodeProof.relation_calibration, SourceTermGraph.output] using
        payload_step (Nat.pair a.encode b.encode) 0 (by decide)
  | less a b =>
      simpa [SourceFormula.encode, SourceBooleanGraph.test, SourceBooleanGraph.forest,
        SourceBooleanGraph.predicate, BaseTerm.encode, Nat.unpair_pair, count_calibration,
        SourceRowsCodeProof.relation_calibration, SourceTermGraph.output] using
        payload_step (Nat.pair a.encode b.encode) 1 (by decide)
  | negative p ih =>
      simpa [SourceFormula.encode, SourceBooleanGraph.test, SourceBooleanGraph.forest,
        SourceBooleanGraph.predicate, Formula.encode, ih] using payload_step p.encode 2 (by decide)
  | conjunction p q ihp ihq =>
      have hs := literalNameShift (SourceTermGraph.nodeCount (SourceBooleanGraph.forest p))
        (SourceBooleanGraph.predicate 0 q)
      rw [actualPredicateShift, Nat.add_zero] at hs
      simpa [SourceFormula.encode, SourceBooleanGraph.test, SourceBooleanGraph.forest,
        SourceBooleanGraph.predicate, BaseTerm.encode, Formula.encode, Nat.unpair_pair, ihp, ihq,
        count_calibration, hs] using
        payload_step (Nat.pair p.encode q.encode) 3 (by decide)
  | existsNat i p ih =>
      simpa [SourceFormula.encode, SourceBooleanGraph.test, SourceBooleanGraph.forest,
        SourceBooleanGraph.predicate, Formula.encode, Nat.unpair_pair, ih] using
        payload_step (Nat.pair i p.encode) 4 (by decide)

theorem test_calibration (p : SourceFormula) : Code.test p.encode = SourceBooleanGraph.test p :=
  congrArg Prod.fst (literalPayload p)
theorem forest_calibration (p : SourceFormula) : Code.forest p.encode = (SourceBooleanGraph.forest p).encode :=
  congrArg (fun x => x.2.1) (literalPayload p)
theorem predicate_calibration (p : SourceFormula) :
    Code.predicate p.encode = (SourceBooleanGraph.predicate 0 p).encode :=
  congrArg (fun x => x.2.2) (literalPayload p)
theorem start_calibration (p : SourceFormula) : Code.start p.encode = SourceBooleanGraph.start p := by
  rw [Code.start, forest_calibration, SourceTermGraphCodeProof.instructions_calibration]
  rfl

theorem graph_calibration (p : SourceFormula) :
    Code.graph p.encode = (SourceTermGraph.graph (SourceBooleanGraph.start p) (SourceBooleanGraph.forest p)).encode := by
  rw [Code.graph, forest_calibration, SourceTermGraphCodeProof.instructions_calibration, start_calibration,
    SourceTermGraphCodeProof.rowMachineCalibration]
  simp only [List.nil_append, SourceTermGraphCodeProof.equations_calibration]
  rfl

theorem compile_calibration (p : SourceFormula) : Code.compile p.encode = (SourceBooleanGraph.compile p).encode := by
  rw [Code.compile, graph_calibration, start_calibration, predicate_calibration,
    literalNameShift, actualPredicateShift, Nat.add_zero]
  rfl

theorem literalCompilation : SourceBooleanProgramsTargets.LiteralCompilation :=
  fun p => ⟨start_calibration p, compile_calibration p⟩

theorem decideExists_calibration (p : SourceFormula) : Code.decideExists p.encode = SourceBooleanGraph.decideExists p := by
  rw [Code.decideExists, test_calibration, compile_calibration, PlainFrontierProgramsProof.answer_calibration]
  rfl

theorem decideForall_calibration (p : SourceFormula) : Code.decideForall p.encode = SourceBooleanGraph.decideForall p := by
  change (Code.decideExists (SourceFormula.negative p).encode).map Bool.not = _
  rw [decideExists_calibration]
  rfl

theorem literalDecisions : SourceBooleanProgramsTargets.LiteralDecisions :=
  fun p => ⟨decideExists_calibration p, decideForall_calibration p⟩

theorem actualEncodedDecisions : SourceBooleanProgramsTargets.ActualEncodedDecisions := by
  intro p hp b
  rw [decideExists_calibration, decideForall_calibration]
  exact ⟨SourceBooleanGraphProof.actualExistentialDecision p hp b,
    SourceBooleanGraphProof.actualUniversalDecision p hp b⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
