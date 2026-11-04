module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryShift
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedAuxiliaryShiftSupportProof NumberedAuxiliaryShiftPrimrecProof

theorem packedWeakeningPrimitive : NumberedAuxiliaryShiftTargets.ActualPackedWeakeningPrimitive := by
  intro n arity Gamma sigma
  have ht : Primrec (fun q : Packed (Fin n) arity Gamma => q.1) :=
    Primrec.fst.comp (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma)
  have hc : Primrec (fun q : Packed (Fin n) arity Gamma => shiftCode 0 (termCode q.2)) :=
    (codeShiftPrimitive n).comp ((Primrec.const 0).pair
      (Primrec.snd.comp (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma)))
  have hn : Primrec (fun q : Packed (Fin n) arity Gamma =>
      Nat.pair (typeNumber q.1) (codeNumber (shiftCode 0 (termCode q.2)))) :=
    Primrec₂.natPair.comp (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp ht)
      ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp hc)
  have hd := (NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity (sigma::Gamma)).comp hn
  have h := Primrec.option_getD.comp hd
    (Primrec.const (⟨Ty.ground,AuxTerm.bottom Ty.ground⟩ : Packed (Fin n) arity (sigma::Gamma)))
  apply h.of_eq
  intro q
  have he : termCode (rename q.2 (Renaming.weaken Gamma sigma))=shiftCode 0 (termCode q.2) :=
    typedShiftCalibration (Fin n) arity [] Gamma sigma q.1 q.2
  change (decodePackedNumber n arity (sigma::Gamma)
    (Nat.pair (typeNumber q.1) (codeNumber (shiftCode 0 (termCode q.2))))).getD _=weakenPacked sigma q
  rw [←he]
  change (decodePackedNumber n arity (sigma::Gamma) (packedNumber (weakenPacked sigma q))).getD _=weakenPacked sigma q
  rw [NumberedNumericDecodingProof.packedNumericRoundTrip]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftProof
