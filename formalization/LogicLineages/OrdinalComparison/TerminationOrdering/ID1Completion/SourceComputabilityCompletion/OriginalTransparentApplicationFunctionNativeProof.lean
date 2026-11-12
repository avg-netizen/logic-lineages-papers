module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeGeometryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeProof
open OriginalTransparentApplicationFunctionNativeTypedProof
open OriginalTransparentApplicationFunctionNativeGeometryProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedNumericCarrier NumberedNumericDecoding NumberedNumericStep NumberedStepCertificate
open OriginalTransparentApplicationFunctionDefinitions OriginalTransparentApplicationFunctionEvaluationProof
open InternalOriginalUniformApplicationStepSelection InternalOriginalUniformParameterLeaves
open OriginalLambdaGuardLeafEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Source decoding is paid by actual sourceValue. Target malformedness is
handled by the typed all-target identity, never by an added endpoint oracle. -/
theorem leafEquality (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
 (hs : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1)
 (hstruct : evaluate structuralGuard v = 1) :
 leafValue n arity (childValues v) = leafValue n arity v := by
 have htag := sourceTag v hstruct
 obtain ⟨Gamma,hGamma⟩ :=
  InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2 (v.get 0) (v.get 3)
 cases hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 with
 | none =>
   simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Matrix.tail_cons,decodedValue,hcontext] at hs
   exact False.elim (Nat.zero_ne_one hs)
 | some ctx =>
   simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Matrix.tail_cons,decodedValue,hcontext,hGamma] at hs
   cases hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) with
   | none =>
     change (decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0)).isSome.toNat = 1 at hs
     rw [hq] at hs
     exact False.elim (Nat.zero_ne_one hs)
   | some q =>
     have hraw := (NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) q).mp hq
     obtain ⟨tau,q⟩ := q
     have he := hraw.1
     rw [← he] at htag
     cases q
     case app =>
       exact typedEquality n arity v ctx Gamma _ _ _ _ hcontext hGamma he.symm hq hstruct
     all_goals simp [packedNumber,termCode,codeNumber] at htag
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeProof
