module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardCalibrationProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedNumericDecoding OriginalUniverseDecoder
open OriginalTypedDecoder (encodeRequest termRequestValue argumentsRequestValue)
open OriginalTypedDecoderExpansionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem originalMemberCalibration (n : Nat) (member : Program 2)
    (hm : ∀ v, evaluate member v = InternalOriginalUniformParameterLeaves.memberValue n v) :
    ContextMemberCalibrated n (InternalOriginalUniformContextMembership.contextMember member) := by
  intro v
  rw [InternalOriginalUniformContextMembershipEvaluationProof.contextMemberEvaluation,hm]
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (Nat.pair (v.get 1) 0)
  simp only [InternalOriginalUniformParameterLeaves.memberValue,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold InternalOriginalUniformParameterLeaves.decodedValue
  rw [hGamma]
  simp only [Nat.unpair_pair]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 1) <;>
    simp [contextMemberValue,hc]

theorem memberEncoded (n : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (tau : Ty) :
    contextMemberValue n (typeNumber tau) (Encodable.encode ctx) = (decide (tau ∈ ctx.1.2)).toNat := by
  simp [contextMemberValue,Encodable.encodek,InternalStructuralEndpointGuard.membershipValue,
    NumberedNumericDecodingSupportProof.typeRoundTrip]

theorem windowEncoded (n : Nat) (arity : Fin n → Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (head : HeadCode (Fin n)) :
    headWindowValue n arity (headNumber head) (Encodable.encode ctx) =
      (decide (NumberedFiniteUniverse.HeadInWindow arity ctx.1.1 ctx.1.2 (decodeHead head))).toNat := by
  simp [headWindowValue,Encodable.encodek,NumberedNumericDecodingSupportProof.headNumericRoundTrip]

theorem andBits (a b : Bool) :
    (if a.toNat = 1 then if b.toNat = 1 then 1 else 0 else 0) = (a && b).toNat := by
  cases a <;> cases b <;> rfl

theorem singleBit (a : Bool) : (if a.toNat = 1 then 1 else 0) = a.toNat := by
  cases a <;> rfl

theorem guardEncoded (n : Nat) (arity : Fin n → Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (request : NumberedTypedRequests.Request n) :
    guardValue (contextMemberValue n) (headWindowValue n arity)
      (encodeRequest request) (Encodable.encode ctx) =
        (NumberedUniverseRequests.guard arity ctx.1.1 ctx.1.2 request).toNat := by
  cases request with
  | arguments Gamma types code =>
    simp [guardValue,encodeRequest,NumberedUniverseRequests.guard]
  | term Gamma tau code =>
    cases code <;>
      simp [guardValue,encodeRequest,codeNumber,memberEncoded,windowEncoded,
        NumberedUniverseRequests.guard,andBits,singleBit] <;> split_ifs <;> simp_all

theorem actualOriginalUniverseGuardCalibration :
    OriginalUniverseDecoderTargets.ActualOriginalUniverseGuardCalibration :=
  ⟨originalMemberCalibration,OriginalUniverseDecoderGuardEvaluationProof.guardEvaluation,guardEncoded⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardCalibrationProof
