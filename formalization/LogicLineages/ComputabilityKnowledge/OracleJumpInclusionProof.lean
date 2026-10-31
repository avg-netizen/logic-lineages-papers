module

public import LogicLineages.ComputabilityKnowledge.OracleJumpInclusionTargets
public import LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormProof
public import LogicLineages.ComputabilityKnowledge.OraclePiThreeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleJumpInclusionProof
open OracleJumpInclusion OracleJumpInclusionTargets OracleJump OraclePiThree
open OracleThirdJumpNormalForm

theorem liftedSecondMatrixPrimitiveRecursive : LiftedSecondMatrixPrimitiveRecursive := by
  have hy : Primrec (fun a : Nat × Nat × Nat × Nat => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hz : Primrec (fun a : Nat × Nat × Nat × Nat => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have h := OracleThirdJumpNormalFormProof.explicitMatricesPrimitiveRecursive.2.1.comp
    (Primrec.fst.pair (hy.pair hz))
  apply h.of_eq
  intro a
  dsimp only [liftedSecondMatrix]

theorem actualSecondIndicatorCalibration : ActualSecondIndicatorCalibration := by
  classical
  intro q
  have hn : (∀ x, ∃ y, ∀ z, liftedSecondMatrix (q, x, y, z) = true) ↔ secondJump q = 1 := by
    constructor
    · intro h
      exact (OracleThirdJumpNormalFormProof.actualSecondJumpNormalForm q).mpr (h 0)
    · intro h x
      exact (OracleThirdJumpNormalFormProof.actualSecondJumpNormalForm q).mp h
  unfold matrixIndicator
  split_ifs with h
  · exact (hn.mp h).symm
  · have hb : secondJump q = 0 ∨ secondJump q = 1 := by
      unfold secondJump jump
      split_ifs <;> simp
    rcases hb with hz | ho
    · exact hz.symm
    · exact False.elim (h (hn.mpr ho))

theorem actualSecondToThirdJumpInclusion : ActualSecondToThirdJumpInclusion := by
  have h := OraclePiThreeProof.actualPiThreeThirdJumpDecision liftedSecondMatrix
    liftedSecondMatrixPrimitiveRecursive
  apply h.of_eq
  intro q
  exact congrArg Part.some (actualSecondIndicatorCalibration q)

end LogicLineages.ComputabilityKnowledge.OracleJumpInclusionProof
