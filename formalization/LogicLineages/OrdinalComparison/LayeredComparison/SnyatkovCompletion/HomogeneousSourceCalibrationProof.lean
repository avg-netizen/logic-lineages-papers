module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceCodeShapeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
open HomogeneousSource

theorem peelExists_calibration (p : SourceFormula) :
    Code.peelExists p.encode = ((peelExists p).1, (peelExists p).2.encode) := by
  induction p with
  | equal a b => simpa [SourceFormula.encode, peelExists] using exists_step (Nat.pair a.encode b.encode) 0 (by decide)
  | less a b => simpa [SourceFormula.encode, peelExists] using exists_step (Nat.pair a.encode b.encode) 1 (by decide)
  | negative p ih => simpa [SourceFormula.encode, peelExists] using exists_step p.encode 2 (by decide)
  | conjunction p q ihp ihq =>
      simpa [SourceFormula.encode, peelExists] using exists_step (Nat.pair p.encode q.encode) 3 (by decide)
  | existsNat i p ih =>
      simpa [SourceFormula.encode, peelExists, Nat.unpair_pair, ih] using exists_step (Nat.pair i p.encode) 4 (by decide)

theorem peelForall_calibration (p : SourceFormula) :
    Code.peelForall p.encode = ((peelForall p).1, (peelForall p).2.encode) := by
  cases p with
  | equal a b => simpa [SourceFormula.encode, peelForall] using forall_outer (Nat.pair a.encode b.encode) 0 (by decide) (by decide)
  | less a b => simpa [SourceFormula.encode, peelForall] using forall_outer (Nat.pair a.encode b.encode) 1 (by decide) (by decide)
  | conjunction p q => simpa [SourceFormula.encode, peelForall] using forall_outer (Nat.pair p.encode q.encode) 3 (by decide) (by decide)
  | existsNat i p => simpa [SourceFormula.encode, peelForall] using forall_outer (Nat.pair i p.encode) 4 (by decide) (by decide)
  | negative q =>
      cases q with
      | equal a b => simpa [SourceFormula.encode, peelForall] using forall_middle (Nat.pair a.encode b.encode) 0 (by decide) (by decide)
      | less a b => simpa [SourceFormula.encode, peelForall] using forall_middle (Nat.pair a.encode b.encode) 1 (by decide) (by decide)
      | negative p => simpa [SourceFormula.encode, peelForall] using forall_middle p.encode 2 (by decide) (by decide)
      | conjunction p q => simpa [SourceFormula.encode, peelForall] using forall_middle (Nat.pair p.encode q.encode) 3 (by decide) (by decide)
      | existsNat i r =>
          cases r with
          | equal a b => simpa [SourceFormula.encode, peelForall] using forall_inner i (Nat.pair a.encode b.encode) 0 (by decide)
          | less a b => simpa [SourceFormula.encode, peelForall] using forall_inner i (Nat.pair a.encode b.encode) 1 (by decide)
          | conjunction p q => simpa [SourceFormula.encode, peelForall] using forall_inner i (Nat.pair p.encode q.encode) 3 (by decide)
          | existsNat j p => simpa [SourceFormula.encode, peelForall] using forall_inner i (Nat.pair j p.encode) 4 (by decide)
          | negative p =>
              have ih := peelForall_calibration p
              simpa [SourceFormula.encode, peelForall, ih] using forall_inner i p.encode 2 (by decide)
termination_by sizeOf p

theorem admissible_calibration (p : SourceFormula) : Code.admissible p.encode = admissible p := by
  unfold Code.admissible admissible
  rw [peelExists_calibration, peelForall_calibration]
  dsimp only
  rw [SourceBooleanProgramsProof.test_calibration, SourceBooleanProgramsProof.test_calibration]

theorem decide_calibration (values : List Nat) (p : SourceFormula) :
    Code.decide values p.encode = decide values p := by
  unfold Code.decide HomogeneousSource.decide
  rw [peelExists_calibration, peelForall_calibration]
  dsimp only
  rw [SourceBooleanProgramsProof.test_calibration,
    SourceParameterDecisionProof.decideExists_calibration, SourceParameterDecisionProof.decideForall_calibration]

theorem literalCodeData : HomogeneousSourceTargets.LiteralCodeData :=
  fun p => ⟨peelExists_calibration p, peelForall_calibration p, admissible_calibration p,
    fun values => decide_calibration values p⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
