module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryBetaPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryBetaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliarySubstitution
open NumberedDirectCertificate NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedAuxiliaryBetaSupportProof NumberedAuxiliaryBetaPrimrecProof

attribute [local irreducible] directTarget substituteCode

theorem betaTypePreservation (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma) (h : directTarget arity Gamma .beta q=some r) : r.1=q.1 := by
  have hi := (NumberedDirectCertificateProof.directRuleCheck n arity Gamma .beta q r).mp h
  cases hi
  rfl

theorem packedBetaPrimitive : NumberedAuxiliarySubstitutionTargets.ActualPackedBetaPrimitive := by
  intro n arity Gamma
  have hs := NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma
  have ht : Primrec (fun q : Packed (Fin n) arity Gamma => typeNumber q.1) :=
    NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp (Primrec.fst.comp hs)
  have hb : Primrec (fun q : Packed (Fin n) arity Gamma => betaCode Gamma.length (termCode q.2)) :=
    (allBetaCodePrimitive n).comp (Primrec.const Gamma.length) (Primrec.snd.comp hs)
  have hn : Primrec (fun p : Packed (Fin n) arity Gamma × Code (Fin n) =>
      Nat.pair (typeNumber p.1.1) (codeNumber p.2)) :=
    Primrec₂.natPair.comp (ht.comp Primrec.fst) ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd)
  have hd := (NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp hn
  have h := Primrec.option_bind hb hd.to₂
  apply h.of_eq
  intro q
  change ((betaCode Gamma.length (termCode q.2)).bind (fun code =>
    decodePackedNumber n arity Gamma (Nat.pair (typeNumber q.1) (codeNumber code))))=directTarget arity Gamma .beta q
  rw [betaCodeCalibration]
  cases hr : directTarget arity Gamma .beta q with
  | none => rfl
  | some r =>
    simp only [Option.map_some,Option.bind_some]
    have ht := betaTypePreservation n arity Gamma q r hr
    rw [←ht]
    exact NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma r

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionProof
