module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedLeastCodeRepresentative
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem typesValue (context : Nat) :
    evaluate contextTypes (ofFn ![context]) = (Nat.unpair (Nat.unpair context).1).2 := by
  rw [contextTypes,unaryCompositionEvaluation,rightEvaluation,leftEvaluation]
  rfl

theorem typesEncoded (n : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) :
    evaluate contextTypes (ofFn ![Encodable.encode ctx]) = Encodable.encode ctx.1.2 := by
  rw [typesValue]
  change (Nat.unpair (Nat.unpair (Nat.pair
    (Nat.pair (Encodable.encode ctx.1.1) (Encodable.encode ctx.1.2))
    (Encodable.encode ctx.2))).1).2 = Encodable.encode ctx.1.2
  rw [Nat.unpair_pair,Nat.unpair_pair]

theorem containsTypes (types : List Source.Ty) (typ : Nat) :
    evaluate contains (ofFn ![Encodable.encode types,typ]) =
      InternalStructuralEndpointGuard.membershipValue types typ := by
  rw [OriginalContextInsertionCalibrationProof.contextNumbers,
    TwoSol20261113.CalibratedPrimary.MembershipNativeProof.actualContainsNative,
    numbersRoundTrip,Option.getD_some]
  obtain ⟨tau,hd,he⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal typ
  rw [InternalStructuralEndpointGuard.membershipValue,hd]
  have hm : typ ∈ types.map typeNumber ↔ tau ∈ types := by
    rw [← he]
    constructor
    · intro h
      obtain ⟨t,ht,heq⟩ := List.mem_map.mp h
      have hh := NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective heq
      simpa only [hh] using ht
    · intro h
      exact List.mem_map.mpr ⟨tau,h,rfl⟩
  simp only [hm]

theorem memberValue (n typ context : Nat) :
    evaluate (member n) (ofFn ![typ,context]) =
      if (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context).isSome.toNat = 0
      then 0 else evaluate contains (ofFn ![evaluate contextTypes (ofFn ![context]),typ]) := by
  rw [member,InternalAcceptanceCalibrationProof.evalBranch,unaryCompositionEvaluation,
    Continuation20261115.OriginalDecodedContextValidity.NativeProof.nativeContext]
  simp only [projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_one,Matrix.cons_val_zero,
    constantEvaluation,binaryCompositionEvaluation,unaryCompositionEvaluation]

theorem nativeOriginalMember : Targets.NativeOriginalMember := by
  intro n v
  have hv : v = ofFn ![v.get 0,v.get 1] := by ext i; fin_cases i <;> rfl
  rw [hv,memberValue]
  change _ = OriginalUniverseDecoder.contextMemberValue n (v.get 0) (v.get 1)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 1) with
  | none => simp only [hc,Option.isSome_none,Bool.toNat_false,ite_true,OriginalUniverseDecoder.contextMemberValue]
  | some ctx =>
    simp only [hc,Option.isSome_some,Bool.toNat_true,Nat.one_ne_zero,ite_false,OriginalUniverseDecoder.contextMemberValue]
    have he := OriginalClassCodes.NativeCodecProof.contextCanonical n (v.get 1) ctx hc
    rw [← he,typesEncoded,containsTypes]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.NativeProof
