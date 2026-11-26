module
public import LogicLineages.PermittedControl.ThresholdTailBridgeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
attribute [local irreducible] ordinalAddCode ordinalSubCode rawNoteEncode rawNormCode rawComparisonCode

 theorem thresholdTailCode_actual (lp mp lq mq : NONote) (B : Nat) :
    thresholdTailCode (intervalPairCodes lp mp lq mq) B=
      max (inverseTableTail lp mp mq (lq-mq) B) (inverseTableTail lq mq mp (lp-mp) B) := by
  have hleft : inverseTableTailCode (rawNoteEncode lp.1) (rawNoteEncode mp.1) (rawNoteEncode mq.1)
      (ordinalSubCode (rawNoteEncode lq.1) (rawNoteEncode mq.1)) B=inverseTableTail lp mp mq (lq-mq) B :=
    (congrArg (fun d => inverseTableTailCode (rawNoteEncode lp.1) (rawNoteEncode mp.1)
      (rawNoteEncode mq.1) d B) (ordinal_sub_note_code lq mq)).trans (inverseTableTailCode_correct lp mp mq (lq-mq) B)
  have hright : inverseTableTailCode (rawNoteEncode lq.1) (rawNoteEncode mq.1) (rawNoteEncode mp.1)
      (ordinalSubCode (rawNoteEncode lp.1) (rawNoteEncode mp.1)) B=inverseTableTail lq mq mp (lp-mp) B :=
    (congrArg (fun d => inverseTableTailCode (rawNoteEncode lq.1) (rawNoteEncode mq.1)
      (rawNoteEncode mp.1) d B) (ordinal_sub_note_code lp mp)).trans (inverseTableTailCode_correct lq mq mp (lp-mp) B)
  exact congrArg₂ max hleft hright

end LogicLineages.PermittedControl
