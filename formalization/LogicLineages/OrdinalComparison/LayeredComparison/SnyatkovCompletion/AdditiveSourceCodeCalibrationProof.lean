module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceProof
open CommonLayerSyntax AdditiveSource

private theorem instructions_test (t : BaseTerm) :
    (SourceTermGraph.instructions t).all (fun op => op.1 != 3) = termTest t := by
  induction t with
  | numeral n => rfl
  | «variable» i => rfl
  | add a b iha ihb => simp [SourceTermGraph.instructions, termTest, List.all_append, iha, ihb]
  | phi a ih => simp [SourceTermGraph.instructions, termTest, List.all_append]

theorem termTest_calibration (t : BaseTerm) : Code.termTest t.encode = termTest t := by
  rw [Code.termTest, SourceTermGraphCodeProof.instructions_calibration, instructions_test]

private theorem test_step (n tag : Nat) (ht : tag < 5) :
    Code.test (5 * n + tag) =
      if tag = 0 ∨ tag = 1 then Code.termTest n.unpair.1 && Code.termTest n.unpair.2
      else if tag = 2 then Code.test n
      else if tag = 3 then Code.test n.unpair.1 && Code.test n.unpair.2
      else Code.test n.unpair.2 := by
  have hm : (5 * n + tag) % 5 = tag := by omega
  have hd : (5 * n + tag) / 5 = n := by omega
  rw [Code.test, hm, hd]

theorem test_calibration (p : SourceFormula) : Code.test p.encode = test p := by
  induction p with
  | equal a b =>
      simpa [SourceFormula.encode, test, Nat.unpair_pair, termTest_calibration] using
        test_step (Nat.pair a.encode b.encode) 0 (by decide)
  | less a b =>
      simpa [SourceFormula.encode, test, Nat.unpair_pair, termTest_calibration] using
        test_step (Nat.pair a.encode b.encode) 1 (by decide)
  | negative p ih =>
      simpa [SourceFormula.encode, test, ih] using test_step p.encode 2 (by decide)
  | conjunction p q ihp ihq =>
      simpa [SourceFormula.encode, test, Nat.unpair_pair, ihp, ihq] using
        test_step (Nat.pair p.encode q.encode) 3 (by decide)
  | existsNat i p ih =>
      simpa [SourceFormula.encode, test, Nat.unpair_pair, ih] using
        test_step (Nat.pair i p.encode) 4 (by decide)

theorem eliminate_calibration (p : SourceFormula) :
    Code.eliminate p.encode = (eliminate p).encode := by
  simp only [Code.eliminate, eliminate, SourceRowsCodeProof.translate_calibration,
    QuantifiedLinearProof.eliminate_calibration]

theorem decideClosed_calibration (p : SourceFormula) :
    Code.decideClosed p.encode = decideClosed p := by
  simp only [Code.decideClosed, decideClosed, test_calibration,
    SourceRowsCodeProof.translate_calibration, ClosedLinearProof.decideClosed_calibration]

theorem literalCodeCalibration : AdditiveSourceTargets.LiteralCodeCalibration :=
  ⟨termTest_calibration, test_calibration, eliminate_calibration, decideClosed_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceProof
