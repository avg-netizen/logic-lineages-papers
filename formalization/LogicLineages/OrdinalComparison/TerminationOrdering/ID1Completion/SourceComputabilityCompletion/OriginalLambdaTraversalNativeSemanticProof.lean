module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeSemanticProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientApplication
open OriginalLambdaCanonical OriginalLambdaTraversal OriginalLambdaTraversalSemanticProof
open OriginalLambdaTraversalNativeConstructorProof

/-- Native strong induction generalizes BOTH the actual encoded Gamma and
the raw runtime parameter. The context coordinate alone stays fixed. The
leaf hypothesis is supplied later by the concrete acyclic selected Program;
it is not an internal law or a premise of the frozen refinement target. -/
theorem semanticTyped (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (leaf : Nat → Nat → Nat) (context : Nat)
    (hleaf : ∀ (Gamma : List Ty) (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau)
      (parameter : Nat),
      (Nat.unpair parameter).1 = context →
      Encodable.encode Gamma = (Nat.unpair parameter).2 →
      leaf (packedNumber ⟨tau,q⟩) parameter = representativeCode symbols S ⟨tau,q⟩)
    (Gamma : List Ty) (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau)
    (parameter : Nat) (hcontext : (Nat.unpair parameter).1 = context)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2)
    (hq : InUniverse symbols S q) :
    semanticFold leaf (packedNumber ⟨tau,q⟩) parameter = representativeCode symbols S ⟨tau,q⟩ := by
  suffices allPayloads : ∀ (bound : Nat) (Gamma : List Ty) (tau : Ty)
      (q : AuxTerm (Fin n) arity Gamma tau) (parameter : Nat),
      payloadValue (packedNumber ⟨tau,q⟩) = bound →
      (Nat.unpair parameter).1 = context →
      Encodable.encode Gamma = (Nat.unpair parameter).2 →
      InUniverse symbols S q →
      semanticFold leaf (packedNumber ⟨tau,q⟩) parameter = representativeCode symbols S ⟨tau,q⟩ by
    exact allPayloads _ Gamma tau q parameter rfl hcontext hg hq
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
    intro Gamma tau q parameter hbound hcontext hg hq
    cases q with
    | @app Gamma sigma tau f a =>
      have hf : InUniverse symbols S f := ⟨hq.1.2.1,hq.2.1⟩
      have ha : InUniverse symbols S a := ⟨hq.1.2.2,hq.2.2⟩
      have hlimits : payloadValue (packedNumber ⟨.arrow sigma tau,f⟩) < bound ∧
          payloadValue (packedNumber ⟨sigma,a⟩) < bound := by
        simpa only [applicationPacked,hbound] using applicationPayloadLess f a
      have ef := ih _ hlimits.1 Gamma (.arrow sigma tau) f parameter rfl hcontext hg hf
      have ea := ih _ hlimits.2 Gamma sigma a parameter rfl hcontext hg ha
      change semanticFold leaf (packedNumber (applicationPacked f a)) parameter =
        representativeCode symbols S (applicationPacked f a)
      rw [semanticApplication, ef, ea]
      exact applicationRepresentative n arity symbols S hS Gamma sigma tau f a hf ha
    | @lam Gamma sigma tau b =>
      have hb : InUniverse symbols S b := ⟨hq.1.2.2,hq.2⟩
      have hlimit : payloadValue (packedNumber ⟨tau,b⟩) < bound := by
        simpa only [lambdaPacked,hbound] using lambdaPayloadLess b
      have hc' : (Nat.unpair (childParameterValue (packedNumber (lambdaPacked b)) parameter)).1 =
          context := (childContext _ parameter).trans hcontext
      have hg' := childGamma b parameter hg
      have eb := ih _ hlimit (sigma :: Gamma) tau b
        (childParameterValue (packedNumber (lambdaPacked b)) parameter) rfl hc' hg' hb
      change semanticFold leaf (packedNumber (lambdaPacked b)) parameter =
        representativeCode symbols S (lambdaPacked b)
      rw [semanticLambda, eb]
      exact lambdaRepresentative n arity symbols S hS Gamma sigma tau b hq
    | var v =>
      rw [semanticEquation]
      simpa [tagValue, OriginalHereditaryValidity.tagValue, InternalApplicationValidityStack.tagValue,
        InternalApplicationValidityStack.payloadValue, packedNumber, termCode, codeNumber]
        using hleaf _ _ (.var v) parameter hcontext hg
    | bottom tau =>
      rw [semanticEquation]
      simpa [tagValue, OriginalHereditaryValidity.tagValue, InternalApplicationValidityStack.tagValue,
        InternalApplicationValidityStack.payloadValue, packedNumber, termCode, codeNumber]
        using hleaf _ _ (.bottom tau) parameter hcontext hg
    | ordinary f base =>
      rw [semanticEquation]
      simpa [tagValue, OriginalHereditaryValidity.tagValue, InternalApplicationValidityStack.tagValue,
        InternalApplicationValidityStack.payloadValue, packedNumber, termCode, codeNumber]
        using hleaf _ _ (.ordinary f base) parameter hcontext hg
    | numbered k f tau base types extras =>
      rw [semanticEquation]
      simpa [tagValue, OriginalHereditaryValidity.tagValue, InternalApplicationValidityStack.tagValue,
        InternalApplicationValidityStack.payloadValue, packedNumber, termCode, codeNumber]
        using hleaf _ _ (.numbered k f tau base types extras) parameter hcontext hg

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeSemanticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeSemanticProof
