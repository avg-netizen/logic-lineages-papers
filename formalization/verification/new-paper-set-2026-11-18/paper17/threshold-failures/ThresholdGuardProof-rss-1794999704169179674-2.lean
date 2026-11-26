module
public import LogicLineages.PermittedControl.ThresholdCombinedTailProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
attribute [local irreducible] ordinalAddCode ordinalSubCode rawNoteEncode rawNormCode rawComparisonCode

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

end LogicLineages.PermittedControl
