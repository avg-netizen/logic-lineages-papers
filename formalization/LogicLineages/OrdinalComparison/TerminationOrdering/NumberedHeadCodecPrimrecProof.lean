module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedHeadCodecPrimrec NumberedHeadCodecPrimrecSupportProof

theorem headEncoderPrimitive : NumberedHeadCodecPrimrecTargets.ActualHeadEncoderPrimitive := encoder
theorem headParserPrimitive : NumberedHeadCodecPrimrecTargets.ActualHeadParserPrimitive := parser

theorem headDecoderPrimitive : NumberedHeadCodecPrimrecTargets.ActualHeadDecoderPrimitive := by
  intro n
  have h : Primrec (fun value => (headParse n value).bind
      (fun head => if headNumber head=value then some head else none)) :=
    Primrec.option_bind (parser n)
      (Primrec.ite (Primrec.eq.comp ((encoder n).comp Primrec.snd) Primrec.fst)
        (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  exact h.of_eq (by
    intro value
    cases hp : headParse n value with
    | none => simp [decodeHeadNumber,hp]
    | some head =>
      by_cases he : headNumber head=value <;> simp [decodeHeadNumber,hp,he,Option.filter])

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecProof
