module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.NativeSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.CodecSupportProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedHeadCodecPrimrec
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NativeSupportProof InternalAcceptanceCalibrationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
def decoded {A : Type} [Encodable A] (f : A → Nat) (raw : Nat) : Nat :=
  ((Encodable.decode raw : Option A).map f).getD 0

theorem decodedSum {A B : Type} [Encodable A] [Encodable B] (f : A → Nat) (g : B → Nat) (raw : Nat) :
    decoded (Sum.elim f g) raw = if raw%2=0 then decoded f (raw/2) else decoded g (raw/2) := by
  have hm := Nat.mod_two_of_bodd raw
  unfold decoded
  rw [Encodable.decode_sum_val]
  unfold Encodable.decodeSum
  rw [Nat.div2_val]
  cases hb : Nat.bodd raw with
  | false =>
    simp only [hb,Bool.toNat_false] at hm
    simp only [hm,if_pos rfl]
    cases hd : (Encodable.decode (raw/2) : Option A) <;> rfl
  | true =>
    simp only [hb,Bool.toNat_true] at hm
    simp only [hm,if_neg (by decide : ¬ (1 : Nat)=0)]
    cases hd : (Encodable.decode (raw/2) : Option B) <;> rfl

theorem sumCalibration {A B : Type} [Encodable A] [Encodable B]
    (left right : Program 1) (f : A → Nat) (g : B → Nat)
    (hl : ∀ raw, evaluate left (ofFn ![raw]) = decoded f raw)
    (hr : ∀ raw, evaluate right (ofFn ![raw]) = decoded g raw) (raw : Nat) :
    evaluate (sumCase left right) (ofFn ![raw]) = decoded (Sum.elim f g) raw := by
  rw [sumCaseValue,decodedSum,hl,hr]

theorem booleanCalibration (raw : Nat) :
    evaluate booleanHead (ofFn ![raw]) = decoded (fun b : Bool => if b then Nat.pair 1 0 else 0) raw := by
  simp only [booleanHead,evalBranch,sameOfEvaluation,constantEvaluation,
    pairOfEvaluation,projectionEvaluation,get_ofFn,Matrix.cons_val_zero]
  rcases raw with _ | raw
  · rfl
  rcases raw with _ | raw
  · rfl
  rw [decoded,Encodable.decode_ge_two (raw+2) (by omega)]
  simp only [Option.map_none,Option.getD_none]
  split_ifs <;> omega

theorem payloadValue (tag raw : Nat) :
    evaluate (payloadHead tag) (ofFn ![raw]) = Nat.pair tag raw := by
  simp only [payloadHead,pairOfEvaluation,constantEvaluation,projectionEvaluation,get_ofFn,Matrix.cons_val_zero]

theorem typeDecode (raw : Nat) :
    (Encodable.decode raw : Option Ty) = some (NumberedTypeCodecPrimrec.typeEquiv.symm raw) := by
  have h := Encodable.encodek (NumberedTypeCodecPrimrec.typeEquiv.symm raw)
  rw [OriginalTypeListsEnumeration.CodecProof.typeInverseEncoding] at h
  exact h

theorem typeCalibration (tag raw : Nat) :
    evaluate (payloadHead tag) (ofFn ![raw]) = decoded (fun t : Ty => Nat.pair tag (typeNumber t)) raw := by
  rw [payloadValue,decoded,typeDecode]
  change Nat.pair tag raw = Nat.pair tag (NumberedTypeCodecPrimrec.typeEquiv
    (NumberedTypeCodecPrimrec.typeEquiv.symm raw))
  rw [Equiv.apply_symm_apply]

theorem productCalibration (raw : Nat) :
    evaluate (payloadHead 4) (ofFn ![raw]) =
      decoded (fun p : Ty × Ty => Nat.pair 4 (Nat.pair (typeNumber p.1) (typeNumber p.2))) raw := by
  rw [payloadValue,decoded,Encodable.decode_prod_val]
  rw [typeDecode,typeDecode]
  change Nat.pair 4 raw = Nat.pair 4 (Nat.pair
    (NumberedTypeCodecPrimrec.typeEquiv (NumberedTypeCodecPrimrec.typeEquiv.symm (Nat.unpair raw).1))
    (NumberedTypeCodecPrimrec.typeEquiv (NumberedTypeCodecPrimrec.typeEquiv.symm (Nat.unpair raw).2)))
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply,Nat.pair_unpair]

theorem rankedCalibration (n raw : Nat) :
    evaluate (rankedHead n) (ofFn ![raw]) = decoded (fun i : Fin n => Nat.pair 5 i.val) raw := by
  have he : evaluate (.composition InternalLessThan.ltTest
      ![.projection 0,OriginalRawSyntaxTransport.constant 1 n]) (ofFn ![raw]) =
      evaluate InternalLessThan.ltTest (ofFn ![raw,n]) := by
    change evaluate InternalLessThan.ltTest
      (ofFn ![raw,evaluate (OriginalRawSyntaxTransport.constant 1 n) (ofFn ![raw])]) = _
    rw [constantEvaluation]
  simp only [rankedHead,evalBranch]
  rw [he,constantEvaluation]
  change (if evaluate InternalLessThan.ltTest (ofFn ![raw,n]) = 0 then 0
    else evaluate (payloadHead 5) (ofFn ![raw])) = _
  rw [InternalLessThanEvaluationProof.exactLessThanEvaluation,payloadValue]
  rw [decoded,NumberedHeadCodecPrimrecSupportProof.finDecode]
  split_ifs <;> simp_all
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.CodecSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.CodecSupportProof
