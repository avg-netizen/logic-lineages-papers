module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationProof
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedMultisetCertificate NumberedMultisetNumeric NumberedMultisetPresentation

theorem certificateFieldsPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (certificateEquiv n arity Gamma) := Primrec.of_equiv

theorem certificateConstructPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (certificateEquiv n arity Gamma).symm := Primrec.of_equiv_symm

theorem packedListEncoderPrimitive :
    NumberedMultisetPresentationTargets.ActualPackedListEncoderPrimitive := by
  intro n arity Gamma
  exact NumberedListCodecPrimrecProof.encoderPrimitive.comp
    (Primrec.list_map Primrec.id
      ((NumberedPackedCodecPrimrecProof.packedEncoderPrimitive n arity Gamma).comp Primrec.snd).to₂)

theorem decodePackedNumbersPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (decodePackedNumbers n arity Gamma) := by
  have hstep : Primrec₂ (fun (_ : List Nat)
      (p : Nat × Option (List (Packed (Fin n) arity Gamma))) =>
      (decodePackedNumber n arity Gamma p.1).bind (fun q => p.2.map (q::·))) := by
    change Primrec (fun p : List Nat × (Nat × Option (List (Packed (Fin n) arity Gamma))) =>
      (decodePackedNumber n arity Gamma p.2.1).bind (fun q => p.2.2.map (q::·)))
    apply Primrec.option_bind
      ((NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp
        (Primrec.fst.comp Primrec.snd))
    apply Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const (some [])) hstep).of_eq
    (by intro xs; induction xs <;> simp_all [decodePackedNumbers, Option.map_eq_bind])

theorem packedListDecoderPrimitive :
    NumberedMultisetPresentationTargets.ActualPackedListDecoderPrimitive := by
  intro n arity Gamma
  exact Primrec.option_bind NumberedListCodecPrimrecProof.decoderPrimitive
    ((decodePackedNumbersPrimitive n arity Gamma).comp Primrec.snd).to₂

theorem certificateEncoderPrimitive :
    NumberedMultisetPresentationTargets.ActualCertificateEncoderPrimitive := by
  intro n arity Gamma
  have hf := certificateFieldsPrimitive n arity Gamma
  have hl := packedListEncoderPrimitive n arity Gamma
  have hw : Primrec (fun c : MultisetCertificate n arity Gamma =>
      numbersNumber (c.witnesses.map (fun p => Nat.pair p.1 p.2))) :=
    NumberedListCodecPrimrecProof.encoderPrimitive.comp
      (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hf)))
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)).to₂)
  exact Primrec₂.natPair.comp (hl.comp (Primrec.fst.comp hf))
    (Primrec₂.natPair.comp (hl.comp (Primrec.fst.comp (Primrec.snd.comp hf)))
      (Primrec₂.natPair.comp (hl.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hf)))) hw))

attribute [local irreducible] decodePackedList decodeNumbers decodePackedNumber decodePackedNumbers

theorem decodeCertificatePrimitive :
    NumberedMultisetPresentationTargets.ActualCertificateDecoderPrimitive := by
  intro n arity Gamma
  unfold decodeCertificate
  have hl := packedListDecoderPrimitive n arity Gamma
  have hu : Primrec (fun value : Nat => (Nat.unpair value).2) := Primrec.snd.comp Primrec.unpair
  have hi : Primrec (fun value : Nat => (Nat.unpair value).1) := Primrec.fst.comp Primrec.unpair
  have hw : Primrec (fun xs : List Nat => xs.map Nat.unpair) :=
    Primrec.list_map Primrec.id (Primrec.unpair.comp Primrec.snd).to₂
  apply Primrec.option_bind (g := fun value kept => do
    let removed ← decodePackedList n arity Gamma (Nat.unpair (Nat.unpair value).2).1
    let inserted ← decodePackedList n arity Gamma (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).1
    let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2
    pure (⟨kept,removed,inserted,witnesses.map Nat.unpair⟩ : MultisetCertificate n arity Gamma)) (hl.comp hi)
  change Primrec (fun p : Nat × List (Packed (Fin n) arity Gamma) => do
    let removed ← decodePackedList n arity Gamma (Nat.unpair (Nat.unpair p.1).2).1
    let inserted ← decodePackedList n arity Gamma (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).1
    let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).2
    pure (⟨p.2,removed,inserted,witnesses.map Nat.unpair⟩ : MultisetCertificate n arity Gamma))
  apply Primrec.option_bind (g := fun p removed => do
    let inserted ← decodePackedList n arity Gamma (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).1
    let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).2
    pure (⟨p.2,removed,inserted,witnesses.map Nat.unpair⟩ : MultisetCertificate n arity Gamma))
    (hl.comp (hi.comp (hu.comp Primrec.fst)))
  change Primrec (fun p : (Nat × List (Packed (Fin n) arity Gamma)) ×
      List (Packed (Fin n) arity Gamma) => do
    let inserted ← decodePackedList n arity Gamma (Nat.unpair (Nat.unpair (Nat.unpair p.1.1).2).2).1
    let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1.1).2).2).2
    pure (⟨p.1.2,p.2,inserted,witnesses.map Nat.unpair⟩ : MultisetCertificate n arity Gamma))
  apply Primrec.option_bind (g := fun p inserted => do
    let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1.1).2).2).2
    pure (⟨p.1.2,p.2,inserted,witnesses.map Nat.unpair⟩ : MultisetCertificate n arity Gamma))
    (hl.comp (hi.comp (hu.comp (hu.comp (Primrec.fst.comp Primrec.fst)))))
  change Primrec (fun p : ((Nat × List (Packed (Fin n) arity Gamma)) ×
      List (Packed (Fin n) arity Gamma)) × List (Packed (Fin n) arity Gamma) =>
    (decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1.1.1).2).2).2).bind
      (fun witnesses => some (⟨p.1.1.2,p.1.2,p.2,witnesses.map Nat.unpair⟩ : MultisetCertificate n arity Gamma)))
  apply Primrec.option_bind (g := fun p witnesses =>
      some (⟨p.1.1.2,p.1.2,p.2,witnesses.map Nat.unpair⟩ : MultisetCertificate n arity Gamma))
    (NumberedListCodecPrimrecProof.decoderPrimitive.comp
      (hu.comp (hu.comp (hu.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))
  exact (Primrec.option_some.comp ((certificateConstructPrimitive n arity Gamma).comp
    ((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair (hw.comp Primrec.snd)))))).to₂

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationProof
