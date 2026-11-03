module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessTargets
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding

def ActualRawTypeSound : Prop := ∀ fuel value tau, typeParse fuel value=some tau → typeNumber tau=value

def ActualRawTypeListSound : Prop := ∀ fuel value types, typesParse fuel value=some types → typesNumber types=value

def ActualRawHeadSound : Prop := ∀ n value (head : HeadCode (Fin n)), headParse n value=some head → headNumber head=value

def ActualRawCodeSound : Prop := ∀ n fuel value (code : Code (Fin n)), codeParse n fuel value=some code → codeNumber code=value

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessTargets
