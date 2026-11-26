module
public import LogicLineages.PermittedControl.ThresholdTargets
public import LogicLineages.PermittedControl.OrdinalEndpointCodeProof
public import LogicLineages.OrdinalComparison.RawNormCode
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison


 theorem note_add_repr (a b : NONote) : (a+b).1.repr=a.1.repr+b.1.repr := ONote.repr_add a.1 b.1
 theorem note_sub_repr (a b : NONote) : (a-b).1.repr=a.1.repr-b.1.repr := ONote.repr_sub a.1 b.1

 theorem ordinal_add_note_code (a b : NONote) : ordinalAddCode (rawNoteEncode a.1) (rawNoteEncode b.1)=rawNoteEncode (a+b).1 := by
  rw [ordinalAddCodeLiteral,rawNoteDecodeEncode,rawNoteDecodeEncode]
  rfl

 theorem ordinal_sub_note_code (a b : NONote) : ordinalSubCode (rawNoteEncode a.1) (rawNoteEncode b.1)=rawNoteEncode (a-b).1 := by
  rw [ordinalSubCodeLiteral,rawNoteDecodeEncode,rawNoteDecodeEncode]
  rfl

 theorem normal_norm_code (a : NONote) : rawNormCode (rawNoteEncode a.1)=actualOrdinalNorm a.1.repr :=
  (rawNormCodeCorrect a.1).trans (actualOrdinalNorm_notationCorrespondence a).symm

end LogicLineages.PermittedControl
