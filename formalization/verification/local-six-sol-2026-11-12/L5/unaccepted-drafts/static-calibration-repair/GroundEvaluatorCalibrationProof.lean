module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionWorkingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
open SourceDecision

private theorem term_step (payload tag : Nat) (h : tag < 10) :
    groundTerm (10 * payload + tag) =
      if tag = 0 then payload else if tag = 1 then 0
      else if tag = 2 then groundTerm payload.unpair.1 + groundTerm payload.unpair.2
      else if tag = 3 then groundTerm payload.unpair.1 - groundTerm payload.unpair.2
      else if tag = 4 then payload.unpair.1 * groundTerm payload.unpair.2
      else if tag = 5 then groundTerm payload.unpair.2 / payload.unpair.1
      else if tag = 6 then Phi (groundTerm payload)
      else if tag = 7 then FixedSeedControlResidue.H (groundTerm payload)
      else if tag = 8 then SnyatkovInverse.phiInverse (groundTerm payload)
      else SnyatkovInverse.hyperInverse (groundTerm payload) := by
  have hm : (10 * payload + tag) % 10 = tag := by omega
  have hd : (10 * payload + tag) / 10 = payload := by omega
  rw [groundTerm, hm, hd]

theorem groundTermCalibration : SourceDecisionTargets.GroundTermCalibration := by
  intro t
  induction t with
  | numeral n =>
    change groundTerm (10 * n + 0) = n
    rw [term_step _ 0 (by decide)]; rfl
  | «variable» i => rw [Term.encode, term_step _ 1 (by decide)]; rfl
  | add a b ha hb =>
    rw [Term.encode, term_step _ 2 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, ha, hb, Term.value]
  | subtract a b ha hb =>
    rw [Term.encode, term_step _ 3 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, ha, hb, Term.value]
  | multiply c a ha =>
    rw [Term.encode, term_step _ 4 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, ha, Term.value]
  | divide c a ha =>
    rw [Term.encode, term_step _ 5 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, ha, Term.value]
  | phi a ha =>
    rw [Term.encode, term_step _ 6 (by decide)]
    simp only [reduceIte, ha, Term.value]
  | hyper a ha =>
    rw [Term.encode, term_step _ 7 (by decide)]
    simp only [reduceIte, ha, Term.value]
  | phiInverse a ha =>
    rw [Term.encode, term_step _ 8 (by decide)]
    simp only [reduceIte, ha, Term.value]
  | hyperInverse a ha =>
    rw [Term.encode, term_step _ 9 (by decide)]
    simp only [reduceIte, ha, Term.value]

private theorem matrix_step (payload tag : Nat) (h : tag < 8) :
    groundMatrix (8 * payload + tag) =
      if tag = 0 then true else if tag = 1 then false
      else if tag = 2 then groundTerm payload.unpair.1 == groundTerm payload.unpair.2
      else if tag = 3 then decide (groundTerm payload.unpair.1 < groundTerm payload.unpair.2)
      else if tag = 4 then decide (payload.unpair.1 ∣ groundTerm payload.unpair.2)
      else if tag = 5 then !(groundMatrix payload)
      else if tag = 6 then groundMatrix payload.unpair.1 && groundMatrix payload.unpair.2
      else groundMatrix payload.unpair.1 || groundMatrix payload.unpair.2 := by
  have hm : (8 * payload + tag) % 8 = tag := by omega
  have hd : (8 * payload + tag) / 8 = payload := by omega
  rw [groundMatrix, hm, hd]

theorem groundMatrixCalibration : SourceDecisionTargets.GroundMatrixCalibration := by
  intro p
  induction p with
  | truth => change groundMatrix (8 * 0 + 0) = true ↔ True; rw [matrix_step _ 0 (by decide)]; simp
  | falsity => change groundMatrix (8 * 0 + 1) = true ↔ False; rw [matrix_step _ 1 (by decide)]; simp
  | equal a b =>
    rw [Matrix.encode, matrix_step _ 2 (by decide)]
    simp [groundTermCalibration, Matrix.eval]
  | less a b =>
    rw [Matrix.encode, matrix_step _ 3 (by decide)]
    simp [groundTermCalibration, Matrix.eval]
  | divisible m a =>
    rw [Matrix.encode, matrix_step _ 4 (by decide)]
    simp [groundTermCalibration, Matrix.eval]
  | negative p hp =>
    rw [Matrix.encode, matrix_step _ 5 (by decide)]
    simpa only [reduceIte, Bool.not_eq_true, Bool.eq_false_iff, Matrix.eval] using not_congr hp
  | conjunction p q hp hq =>
    rw [Matrix.encode, matrix_step _ 6 (by decide)]
    simpa only [reduceIte, Nat.unpair_pair, Bool.and_eq_true, Matrix.eval] using and_congr hp hq
  | disjunction p q hp hq =>
    rw [Matrix.encode, matrix_step _ 7 (by decide)]
    simpa only [reduceIte, Nat.unpair_pair, Bool.or_eq_true, Matrix.eval] using or_congr hp hq

#print axioms groundTermCalibration
#print axioms groundMatrixCalibration
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
