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

/-- Pure arithmetic shape of the original norm guard. All ordinal-norm and
tail terms are abstract naturals here, so no decision procedure ever
compares the actual ordinal terms. -/
 theorem threshold_guard_arithmetic (a k m r t : Nat)
    (h : 1+max (max 2 (max a (max k m))) r≤t) : max 2 (max a m)≤t := by omega

 theorem threshold_left_tail (lp mp lq mq : NONote) (B t : Nat)
    (ht : thresholdTailCode (intervalPairCodes lp mp lq mq) B≤t) :
    inverseTableTail lp mp mq (lq-mq) B≤t :=
  (le_max_left _ _).trans ((thresholdTailCode_actual lp mp lq mq B).symm.trans_le ht)

 theorem threshold_right_tail (lp mp lq mq : NONote) (B t : Nat)
    (ht : thresholdTailCode (intervalPairCodes lp mp lq mq) B≤t) :
    inverseTableTail lq mq mp (lp-mp) B≤t :=
  (le_max_right _ _).trans ((thresholdTailCode_actual lp mp lq mq B).symm.trans_le ht)

 theorem threshold_original_guard (lp mp lq mq : NONote) (B t : Nat)
    (ht : thresholdTailCode (intervalPairCodes lp mp lq mq) B≤t) :
    max 2 (max (actualOrdinalNorm lp.1.repr) (actualOrdinalNorm mp.1.repr))≤t ∧
    max 2 (max (actualOrdinalNorm lq.1.repr) (actualOrdinalNorm mq.1.repr))≤t := by
  have hl := threshold_left_tail lp mp lq mq B t ht
  have hr := threshold_right_tail lp mp lq mq B t ht
  dsimp only [inverseTableTail] at hl hr
  exact ⟨threshold_guard_arithmetic _ _ _ _ _ hl,threshold_guard_arithmetic _ _ _ _ _ hr⟩

end LogicLineages.PermittedControl
