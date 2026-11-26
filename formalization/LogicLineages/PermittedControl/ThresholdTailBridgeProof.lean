module
public import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
attribute [local irreducible] ordinalAddCode ordinalSubCode rawNoteEncode rawNormCode rawComparisonCode

 theorem normal_encoded_gap_tail (a b c d : NONote) (k : Nat) :
    encodedGapInputTail (rawNoteEncode a.1,rawNoteEncode b.1,rawNoteEncode c.1,rawNoteEncode d.1,k)=
      gapInputTail a.1.repr b.1.repr c.1.repr d.1.repr k := by
  simp only [encodedGapInputTail,gapInputTail,gapProfileBound]
  rw [normal_norm_code a,normal_norm_code b,normal_norm_code c,normal_norm_code d]

 theorem inverseTableTailCode_correct (lambda mu nu delta : NONote) (B : Nat) :
    inverseTableTailCode (rawNoteEncode lambda.1) (rawNoteEncode mu.1) (rawNoteEncode nu.1)
      (rawNoteEncode delta.1) B=inverseTableTail lambda mu nu delta B := by
  have hk : rawNormCode (ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode delta.1))=
      actualOrdinalNorm (mu.1.repr+delta.1.repr) := by
    rw [ordinal_add_note_code,normal_norm_code,note_add_repr]
  have hleft : encodedGapInputTail (ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode delta.1),
      rawNoteEncode mu.1,ordinalAddCode (rawNoteEncode nu.1) (rawNoteEncode delta.1),rawNoteEncode nu.1,0)=
      gapInputTail (mu.1.repr+delta.1.repr) mu.1.repr (nu.1.repr+delta.1.repr) nu.1.repr 0 := by
    rw [ordinal_add_note_code,ordinal_add_note_code]
    have hh := normal_encoded_gap_tail (mu+delta) mu (nu+delta) nu 0
    simpa only [note_add_repr] using hh
  have hright : encodedGapInputTail (ordinalAddCode (rawNoteEncode nu.1) (rawNoteEncode delta.1),
      rawNoteEncode nu.1,ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode delta.1),rawNoteEncode mu.1,0)=
      gapInputTail (nu.1.repr+delta.1.repr) nu.1.repr (mu.1.repr+delta.1.repr) mu.1.repr 0 := by
    rw [ordinal_add_note_code,ordinal_add_note_code]
    have hh := normal_encoded_gap_tail (nu+delta) nu (mu+delta) mu 0
    simpa only [note_add_repr] using hh
  simp only [inverseTableTailCode,inverseTableTail,hk,hleft,hright,
    normal_norm_code lambda,normal_norm_code mu]

end LogicLineages.PermittedControl
