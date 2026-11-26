module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadSignaturePrimrecProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderHeadSelectionProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding OriginalTypedDecoder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

/-- Only the original head decoder and its finite signature are compiled. -/
theorem headSignaturePrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (headSignatureValue n arity) := by
  have hr : Primrec (fun head : HeadCode (Fin n) => typeNumber (headResult (decodeHead head))) :=
    NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp
      (NumberedHeadSignaturePrimrecProof.headResultPrimitive n)
  have ha : Primrec (fun head : HeadCode (Fin n) => typesNumber (headArguments arity (decodeHead head))) :=
    NumberedTypeCodecPrimrecProof.typeListEncoderPrimitive.comp
      (NumberedHeadSignaturePrimrecProof.headArgumentsPrimitive n arity)
  have hb : Primrec (fun p : Nat × HeadCode (Fin n) =>
      1 + Nat.pair (typeNumber (headResult (decodeHead p.2)))
        (typesNumber (headArguments arity (decodeHead p.2)))) :=
    Primrec.nat_add.comp (Primrec.const 1)
      (Primrec₂.natPair.comp (hr.comp Primrec.snd) (ha.comp Primrec.snd))
  have h := Primrec.option_casesOn
    (NumberedHeadCodecPrimrecProof.headDecoderPrimitive n) (Primrec.const 0) hb.to₂
  exact h.of_eq (by
    intro value
    unfold headSignatureValue
    cases decodeHeadNumber n value <;> rfl)

theorem headSignatureVectorPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun v : List.Vector Nat 1 => headSignatureValue n arity (v.get 0)) :=
  (headSignaturePrimitive n arity).comp
    (Primrec.vector_get.comp Primrec.id (Primrec.const 0))

theorem actualOriginalTypedHeadSelection :
    OriginalTypedDecoderTargets.ActualOriginalTypedHeadSelection := by
  intro n arity
  exact Proof.allPrimitiveFunctions 1 _ (headSignatureVectorPrimitive n arity)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderHeadSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderHeadSelectionProof
