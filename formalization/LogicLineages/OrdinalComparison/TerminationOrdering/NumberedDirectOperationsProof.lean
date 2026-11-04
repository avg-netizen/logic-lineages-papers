module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCodePrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction NumberedDirectCertificate
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedDirectOperations
open NumberedDirectCodePrimrecProof NumberedDirectOperationsSupportProof

attribute [local irreducible] Primrec directTarget

theorem reconstructSameType {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {A : Type} [Primcodable A] (source : A → Packed (Fin n) arity Gamma)
    (target : A → Option (Packed (Fin n) arity Gamma)) (raw : A → Option (Code (Fin n)))
    (hs : Primrec source) (hr : Primrec raw)
    (hc : ∀ a,raw a=(target a).map (fun r => termCode r.2))
    (ht : ∀ a r,target a=some r → r.1=(source a).1) : Primrec target := by
  have htype : Primrec (fun a => typeNumber (source a).1) :=
    NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp
      (Primrec.fst.comp ((NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp hs))
  have hn : Primrec (fun p : A × Code (Fin n) =>
      Nat.pair (typeNumber (source p.1).1) (codeNumber p.2)) :=
    Primrec₂.natPair.comp (htype.comp Primrec.fst) ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd)
  have hd := (NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp hn
  have h := Primrec.option_bind hr hd.to₂
  apply h.of_eq
  intro a
  change ((raw a).bind (fun code => decodePackedNumber n arity Gamma
    (Nat.pair (typeNumber (source a).1) (codeNumber code))))=target a
  rw [hc a]
  cases htarget : target a with
  | none => rfl
  | some r =>
    simp only [Option.map_some,Option.bind_some]
    rw [←ht a r htarget]
    exact NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma r

theorem packedPutPrimitive : NumberedDirectOperationsTargets.ActualPackedPutPrimitive := by
  intro n arity Gamma
  have hp : Primrec (fun p : Nat × Packed (Fin n) arity Gamma =>
      (p.1,packedCode p.2)) :=
    Primrec.fst.pair ((NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp Primrec.snd)
  have hr : Primrec (fun p : Nat × Packed (Fin n) arity Gamma => putCode p.1 p.2.1 (termCode p.2.2)) :=
    (putCodePrimitive n).comp hp
  exact reconstructSameType Prod.snd (fun p => directTarget arity Gamma (.put p.1) p.2)
    (fun p => putCode p.1 p.2.1 (termCode p.2.2)) Primrec.snd hr
    (fun p => putCodeCalibration n arity Gamma p.1 p.2)
    (fun p r h => directTypePreservation n arity Gamma (.put p.1) p.2 r h)

theorem packedAbstractionPrimitive : NumberedDirectOperationsTargets.ActualPackedAbstractionPrimitive := by
  intro n arity Gamma
  have hr : Primrec (fun q : Packed (Fin n) arity Gamma => abstractionCode (termCode q.2)) :=
    (allAbstractionCodePrimitive n).comp
      (Primrec.snd.comp (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma))
  exact reconstructSameType id (directTarget arity Gamma .abstraction)
    (fun q => abstractionCode (termCode q.2)) Primrec.id hr
    (abstractionCodeCalibration n arity Gamma)
    (fun q r h => directTypePreservation n arity Gamma .abstraction q r h)

theorem packedBottomPrimitive : NumberedDirectOperationsTargets.ActualPackedBottomPrimitive := by
  intro n arity Gamma
  have hr : Primrec (fun q : Packed (Fin n) arity Gamma => bottomCode q.1 (termCode q.2)) :=
    (bottomCodePrimitive n).comp (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma)
  exact reconstructSameType id (directTarget arity Gamma .bottom)
    (fun q => bottomCode q.1 (termCode q.2)) Primrec.id hr
    (bottomCodeCalibration n arity Gamma)
    (fun q r h => directTypePreservation n arity Gamma .bottom q r h)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsProof
