module

public import LogicLineages.OrdinalComparison.RawNotationCode
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_rawNoteEncodeEquation : Targets.RawNoteEncodeEquation :=
  rawNoteEncodeEquation

theorem fixed_rawNoteDecodeEquation : Targets.RawNoteDecodeEquation :=
  rawNoteDecodeEquation

theorem fixed_rawNoteDecodeEncode : Targets.RawNoteDecodeEncode :=
  rawNoteDecodeEncode

theorem fixed_rawNoteEncodeDecode : Targets.RawNoteEncodeDecode :=
  rawNoteEncodeDecode

theorem fixed_rawNoteNormalizationPrimitiveRecursive : Targets.RawNoteNormalizationPrimitiveRecursive :=
  rawNoteNormalizationPrimitiveRecursive

theorem fixed_rawNoteDenumerableFaithful : Targets.RawNoteDenumerableFaithful rawONoteDenumerable :=
  rawNoteDenumerableFaithful

theorem fixed_rawNotePrimcodableFaithful : Targets.RawNotePrimcodableFaithful rawONotePrimcodable :=
  rawNotePrimcodableFaithful

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
