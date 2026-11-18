module
public import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
attribute [local irreducible] ordinalAddCode ordinalSubCode rawNoteEncode rawNormCode rawComparisonCode

 theorem inverseTableTailCode_correct (lambda mu nu delta : NONote) (B : Nat) :
    inverseTableTailCode (rawNoteEncode lambda.1) (rawNoteEncode mu.1) (rawNoteEncode nu.1)
      (rawNoteEncode delta.1) B=inverseTableTail lambda mu nu delta B := by
  dsimp only [inverseTableTailCode,inverseTableTail]
  rw [ordinal_add_note_code,ordinal_add_note_code,
    normal_norm_code lambda,normal_norm_code (mu+delta),normal_norm_code mu,
    (gapInputTailEffective.2 (mu+delta) mu (nu+delta) nu 0),
    (gapInputTailEffective.2 (nu+delta) nu (mu+delta) mu 0)]
  simp only [note_add_repr]

 theorem thresholdTailCode_actual (lp mp lq mq : NONote) (B : Nat) :
    thresholdTailCode (intervalPairCodes lp mp lq mq) B=
      max (inverseTableTail lp mp mq (lq-mq) B) (inverseTableTail lq mq mp (lp-mp) B) := by
  unfold thresholdTailCode intervalPairCodes
  rw [ordinal_sub_note_code,ordinal_sub_note_code,inverseTableTailCode_correct,inverseTableTailCode_correct]

 theorem proper_gap_note (lambda mu : NONote) (hp : Targets.ProperIntervalNotes lambda mu) :
    Order.IsSuccLimit (lambda-mu).1.repr ∧
    mu.1.repr+(lambda-mu).1.repr=lambda.1.repr := by
  simp only [note_sub_repr]
  exact ⟨Ordinal.isSuccLimit_sub hp.1.isSuccPrelimit hp.2.2,
    Ordinal.add_sub_cancel_of_le hp.2.2.le⟩

 theorem threshold_original_guard (lp mp lq mq : NONote) (B t : Nat)
    (ht : thresholdTailCode (intervalPairCodes lp mp lq mq) B≤t) :
    max 2 (max (actualOrdinalNorm lp.1.repr) (actualOrdinalNorm mp.1.repr))≤t ∧
    max 2 (max (actualOrdinalNorm lq.1.repr) (actualOrdinalNorm mq.1.repr))≤t := by
  rw [thresholdTailCode_actual] at ht
  dsimp only [inverseTableTail] at ht
  omega

 theorem threshold_left_tail (lp mp lq mq : NONote) (B t : Nat)
    (ht : thresholdTailCode (intervalPairCodes lp mp lq mq) B≤t) :
    inverseTableTail lp mp mq (lq-mq) B≤t := by rw [thresholdTailCode_actual] at ht; omega

 theorem threshold_right_tail (lp mp lq mq : NONote) (B t : Nat)
    (ht : thresholdTailCode (intervalPairCodes lp mp lq mq) B≤t) :
    inverseTableTail lq mq mp (lp-mp) B≤t := by rw [thresholdTailCode_actual] at ht; omega

 theorem fixed_partner_hit_mem (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lambda mu delta : NONote) (t i : Nat) (hd : Order.IsSuccLimit delta.1.repr)
    (hi : FirstEntry f (countInitial lambda.1.repr t) (mu.1.repr+delta.1.repr) i) :
    (entryNormAt f (countInitial lambda.1.repr t) i,i) ∈ fixedEntryProgram f
      (rawNoteEncode lambda.1,ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode delta.1),t) := by
  rw [ordinal_add_note_code]
  have hc : Computable f := (selected_laws f B hf).2.1.to_comp
  apply ((fixedEntryProgramEffectivity f hc).2 lambda (mu+delta) t _ i
    (Or.inr (by simpa only [note_add_repr] using Ordinal.isSuccLimit_add mu.1.repr hd))).mpr
  exact ⟨by simpa only [note_add_repr] using hi,rfl⟩

end LogicLineages.PermittedControl
