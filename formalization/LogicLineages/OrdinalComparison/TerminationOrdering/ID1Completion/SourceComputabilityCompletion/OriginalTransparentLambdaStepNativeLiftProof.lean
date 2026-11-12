module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftProof
open OriginalTransparentLambdaStepNativeLiftSupportProof OriginalTransparentLambdaStepNativeLiftTypedProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedNumericCarrier NumberedNumericDecoding NumberedNumericStep NumberedStepCertificate
open OriginalHereditaryLambda OriginalLambdaCertificate
open InternalOriginalUniformApplicationStepSelection InternalOriginalUniformParameterLeaves
open OriginalLambdaGuardLeafEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact actual-hop reverse implication. No replacement certificate or context. -/
theorem leafParentAccept (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (hs : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1)
    (hl : evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1)
    (hm : matchingTargetValue v = 1) (hp : lamPathValue v = 1)
    (hc : leafValue n arity (childValues v) = 1) : leafValue n arity v = 1 := by
  have htag := sourceLambdaTag v hl
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (v.get 3)
  cases hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 3)).1 with
  | none =>
    simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.tail_cons,decodedValue,hcontext] at hs
    exact False.elim (Nat.zero_ne_one hs)
  | some ctx =>
    simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons,
      decodedValue,hcontext,hGamma] at hs
    cases hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) with
    | none =>
      change (decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0)).isSome.toNat = 1 at hs
      rw [hq] at hs
      exact False.elim (Nat.zero_ne_one hs)
    | some q =>
      have hraw := (NumberedNumericCarrierProof.numericUniverseDecode n arity
        ctx.1.1 ctx.1.2 Gamma (v.get 0) q).mp hq
      obtain ⟨tau,q⟩ := q
      have he := hraw.1
      rw [← he] at htag
      cases q
      case lam =>
        exact typedParentAccept n arity v ctx Gamma _ _ _ hcontext hGamma he.symm hq hm hp hc
      all_goals simp [packedNumber,termCode,codeNumber] at htag

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftProof
