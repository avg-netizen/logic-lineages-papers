module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceLeavesProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericCarrier
open InternalOriginalUniformParameterLeaves
open InternalOriginalUniformDescentSelection (Data Calibrated)
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrence
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original source, target, and type-membership leaves all accept each
original typed-window frame at its own actual Gamma and retained raw context. -/
theorem typedLeaves (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (context : Nat) (frame : Frame)
    (h : TypedWindowFrame n arity context frame) :
    evaluate data.oldSource (List.Vector.ofFn ![frame.raw,frame.parameter]) = 1 ∧
    evaluate data.oldTarget (List.Vector.ofFn ![frame.raw,frame.parameter]) = 1 ∧
    evaluate data.member (List.Vector.ofFn ![resultTypeValue frame.raw,frame.parameter]) = 1 := by
  obtain ⟨ctx,hctx,Gamma,hparam,tau,q,hraw,htau,hq⟩ := h
  have ho (value : Nat) :
      parameterObject value (Nat.pair context (Encodable.encode Gamma)) = some (Gamma,value) := by
    simp only [parameterObject,Nat.unpair_pair]
    exact Encodable.encodek (Gamma,value)
  have hs : rawCarrierTest n arity ctx.1.1 ctx.1.2 Gamma (packedNumber ⟨tau,q⟩) = true :=
    (NumberedNumericCarrierProof.rawCarrierTestCorrect n arity ctx.1.1 ctx.1.2 Gamma _).mpr
      ⟨⟨tau,q⟩,hq,rfl⟩
  have ht : NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma
      (packedNumber ⟨tau,q⟩) = some (NumberedAuxiliaryCoding.packedCode ⟨tau,q⟩) := by
    rw [NumberedUniformPackedDecodingProof.rawPackedCalibration,
      NumberedNumericDecodingProof.packedNumericRoundTrip]
    rfl
  have hm : InternalStructuralEndpointGuard.membershipValue ctx.1.2 (typeNumber tau) = 1 := by
    simp [InternalStructuralEndpointGuard.membershipValue,
      NumberedNumericDecodingSupportProof.typeRoundTrip,htau]
  rw [hc.1,hc.2.1,hc.2.2.2,hparam,hraw]
  simp only [sourceValue,targetValue,memberValue,decodedValue,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Nat.unpair_pair,hctx,ho,hs,ht,
    Bool.toNat_true,Option.isSome_some]
  exact ⟨trivial,trivial,by simpa only [resultTypeValue,InternalApplicationValidityStack.resultTypeValue,
    packedNumber,Nat.unpair_pair] using hm⟩

theorem typedNode (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (context : Nat) (frame : Frame)
    (h : TypedWindowFrame n arity context frame) :
    nodeCheckValue
      (fun value parameter => evaluate data.oldSource (List.Vector.ofFn ![value,parameter]))
      (fun value parameter => evaluate data.oldTarget (List.Vector.ofFn ![value,parameter]))
      (fun value parameter => evaluate data.member (List.Vector.ofFn ![value,parameter]))
      frame.raw frame.parameter = 1 := by
  obtain ⟨hs,ht,hm⟩ := typedLeaves n arity data hc context frame h
  simp [nodeCheckValue,hs,ht,hm]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceLeavesProof
