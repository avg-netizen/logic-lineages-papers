module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceDescendantProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrence
open OriginalHereditaryValidityRecurrenceSourceRootProof

theorem applicationChildren {n : Nat} {arity : Fin n → Nat} {context : Nat} {frame : Frame}
    (h : TypedWindowFrame n arity context frame) (ht : tagValue frame.raw = 2) :
    TypedWindowFrame n arity context ⟨functionChildValue frame.raw,frame.parameter⟩ ∧
    TypedWindowFrame n arity context ⟨argumentChildValue frame.raw,frame.parameter⟩ := by
  obtain ⟨ctx,hctx,Gamma,hparam,tau,q,hraw,_,hq⟩ := h
  rw [hraw] at ht ⊢
  cases q with
  | app f a =>
    have hf : InUniverse ctx.1.1 ctx.1.2 f := ⟨hq.1.2.1,hq.2.1⟩
    have ha : InUniverse ctx.1.1 ctx.1.2 a := ⟨hq.1.2.2,hq.2.2⟩
    constructor
    · refine ⟨ctx,hctx,Gamma,hparam,_,f,?_,resultInWindow _ _ f hf,hf⟩
      simp [functionChildValue,InternalApplicationValidityStack.functionChildValue,
        InternalApplicationValidityStack.functionValue,InternalApplicationValidityStack.domainValue,
        InternalApplicationValidityStack.bodyValue,InternalApplicationValidityStack.resultTypeValue,
        InternalApplicationValidityStack.functionPayloadValue,InternalApplicationValidityStack.payloadValue,
        packedNumber,termCode,codeNumber,typeNumber]
    · refine ⟨ctx,hctx,Gamma,hparam,_,a,?_,resultInWindow _ _ a ha,ha⟩
      simp [argumentChildValue,InternalApplicationValidityStack.argumentChildValue,
        InternalApplicationValidityStack.argumentValue,InternalApplicationValidityStack.domainValue,
        InternalApplicationValidityStack.bodyValue,InternalApplicationValidityStack.argumentPayloadValue,
        InternalApplicationValidityStack.payloadValue,packedNumber,termCode,codeNumber]
  | _ =>
    simp [tagValue,InternalApplicationValidityStack.tagValue,InternalApplicationValidityStack.payloadValue,
      packedNumber,termCode,codeNumber] at ht

theorem lambdaChild {n : Nat} {arity : Fin n → Nat} {context : Nat} {frame : Frame}
    (h : TypedWindowFrame n arity context frame) (ht : tagValue frame.raw = 1) :
    TypedWindowFrame n arity context
      ⟨lambdaBodyValue frame.raw,childParameterValue frame.raw frame.parameter⟩ := by
  obtain ⟨ctx,hctx,Gamma,hparam,tau,q,hraw,_,hq⟩ := h
  rw [hraw] at ht ⊢
  cases q with
  | @lam _ sigma tau body =>
    have hb : InUniverse ctx.1.1 ctx.1.2 body := ⟨hq.1.2.2,hq.2⟩
    refine ⟨ctx,hctx,sigma :: Gamma,?_,tau,body,?_,resultInWindow _ _ body hb,hb⟩
    · simp [childParameterValue,hparam,domainValue,InternalApplicationValidityStack.domainValue,
        InternalApplicationValidityStack.bodyValue,InternalApplicationValidityStack.payloadValue,
        packedNumber,termCode,codeNumber,OriginalContextExtensionCalibrationProof.contextEncoding,
        OriginalContextExtensionCalibrationProof.typeEncoding,
        Nat.add_comm 1,Nat.succ_eq_add_one]
    · simp [lambdaBodyValue,lambdaCodomainValue,resultTypeValue,
        InternalApplicationValidityStack.resultTypeValue,lambdaBodyPayloadValue,payloadValue,
        InternalApplicationValidityStack.payloadValue,packedNumber,termCode,codeNumber,typeNumber,
        Nat.add_comm 1]
  | _ =>
    simp [tagValue,InternalApplicationValidityStack.tagValue,InternalApplicationValidityStack.payloadValue,
      packedNumber,termCode,codeNumber] at ht

theorem descendantTyped {n : Nat} {arity : Fin n → Nat} {context : Nat} {root frame : Frame}
    (hroot : TypedWindowFrame n arity context root) (h : DescendantFrame root frame) :
    TypedWindowFrame n arity context frame := by
  induction h with
  | root => exact hroot
  | function _ ht ih => exact (applicationChildren ih ht).1
  | argument _ ht ih => exact (applicationChildren ih ht).2
  | body _ ht ih => exact lambdaChild ih ht

theorem actualOriginalHereditarySourceDescendantInvariant :
    OriginalHereditaryValidityRecurrenceTargets.ActualOriginalHereditarySourceDescendantInvariant := by
  intro n arity value parameter h frame hf
  exact descendantTyped (sourceTyped n arity value parameter h) hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceDescendantProof
