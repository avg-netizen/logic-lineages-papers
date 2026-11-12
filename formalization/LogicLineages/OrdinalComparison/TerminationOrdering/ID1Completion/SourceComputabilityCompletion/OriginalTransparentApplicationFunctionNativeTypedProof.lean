module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeTargetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeTypedProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedNumericCarrier NumberedNumericDecoding NumberedNumericStep
open InternalOriginalUniformApplicationStepSelection InternalOriginalUniformParameterLeaves
open OriginalTransparentApplicationFunctionDefinitions OriginalTransparentApplicationFunctionEvaluationProof
open OriginalTransparentApplicationFunctionNativeGeometryProof
open OriginalTransparentLambdaStepNativeLiftSupportProof
open OriginalLambdaGuardLeafEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem typedEquality (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
 (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty) (sigma tau : Ty)
 (q : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma)
 (hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 = some ctx)
 (hGamma : parameterObject (v.get 0) (v.get 3) = some (Gamma,v.get 0))
 (hs : v.get 0 = packedNumber (⟨tau,.app q a⟩ : Packed (Fin n) arity Gamma))
 (hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) = some ⟨tau,.app q a⟩)
 (hstruct : evaluate structuralGuard v = 1) :
 leafValue n arity (childValues v) = leafValue n arity v := by
 let w := InternalApplicationStepPeel.view (state v)
 have hshape := shapeOfGuard v hstruct
 have hc := childrenAtState v
 have hdom : w.domain = typeNumber sigma := by
   simp [w,InternalApplicationStepPeel.view,state,hs,packedNumber,termCode,codeNumber]
 have hcod : w.sourceType = typeNumber tau := by
   simp [w,InternalApplicationStepPeel.view,state,hs,packedNumber]
 have hfn : w.functionPayload = codeNumber (termCode q) := by
   simp [w,InternalApplicationStepPeel.view,state,hs,packedNumber,termCode,codeNumber]
 have harg : w.argumentPayload = codeNumber (termCode a) := by
   simp [w,InternalApplicationStepPeel.view,state,hs,packedNumber,termCode,codeNumber]
 have hfirst : (childValues v).get 0 = packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma) := by
   simpa only [← show w = InternalApplicationStepPeel.view (state v) from rfl,
     InternalApplicationStepPeel.endpointInputs,List.Vector.get_ofFn,Matrix.cons_val_two,
     Matrix.head_cons,Matrix.tail_cons,hdom,hcod,hfn,packedNumber,typeNumber] using hc.1
 have hsecond : (childValues v).get 1 = Nat.pair (typeNumber (.arrow sigma tau)) w.targetFunctionPayload := by
   simpa only [← show w = InternalApplicationStepPeel.view (state v) from rfl,
     InternalApplicationStepPeel.endpointInputs,List.Vector.get_ofFn,Matrix.cons_val_three,
     Matrix.head_cons,Matrix.tail_cons,hdom,hcod,typeNumber] using hc.2.1
 have htarget := InternalApplicationStepCheckerEvaluationProof.targetReconstruction (state v) hshape
 have htarget' : v.get 1 = Nat.pair (typeNumber tau) (Nat.pair 2
   (Nat.pair (typeNumber sigma) (Nat.pair w.targetFunctionPayload (codeNumber (termCode a))))) := by
   have hv : w.target = v.get 1 := by simp [w,InternalApplicationStepPeel.view,state]
   change ApplicationCertificateLift.rawApplication w.domain w.sourceType
     ((InternalApplicationStepPeel.endpointInputs w).get 3)
     ((InternalApplicationStepPeel.endpointInputs w).get 4) = w.target at htarget
   simpa [ApplicationCertificateLift.rawApplication,InternalApplicationStepPeel.endpointInputs,
     hdom,hcod,harg,Nat.unpair_pair,hv] using htarget.symm
 have hcert := InternalApplicationStepCheckerEvaluationProof.certificateReconstruction (state v) hshape
 have hcert' : v.get 2 = ApplicationCertificateLift.liftStep ((childValues v).get 2) := by
   rw [hc.2.2.1]
   simpa only [InternalApplicationStepPeel.view,state,Nat.unpair_pair] using hcert.symm
 have hu := (NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma _ _).mp hq
 have huu := (ApplicationStepGuardProof.actualSourceUniverseDecomposition n arity ctx.1.1 ctx.1.2 Gamma sigma tau q a).mp hu.2
 have he := OriginalTransparentApplicationFunctionNativeTargetProof.allTargetIdentity n arity ctx.1.1 ctx.1.2 Gamma ctx.2
   sigma tau q a w.targetFunctionPayload ((childValues v).get 2) huu.2.1 huu.2.2 huu.1
 have hg := originalGammaCode (v.get 0) (v.get 3) Gamma hGamma
 have ho : parameterObject ((childValues v).get 0) ((childValues v).get 3) = some (Gamma,(childValues v).get 0) := by
   rw [hc.2.2.2]
   have hp : v.get 3 = Nat.pair (Nat.unpair (v.get 3)).1 (Encodable.encode Gamma) := by
     rw [hg,Nat.pair_unpair]
   rw [hp]
   exact encodedParameterObject _ _ _
 have hctx : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
   (Nat.unpair ((childValues v).get 3)).1 = some ctx := by rw [hc.2.2.2]; exact hcontext
 rw [leafAtCoordinates n arity (childValues v) ctx Gamma hctx ho,
   leafAtCoordinates n arity v ctx Gamma hcontext hGamma,hfirst,hsecond,hs,htarget',hcert']
 exact congrArg Bool.toNat he.symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeTypedProof
