module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftTypedProof
open OriginalTransparentLambdaStepNativeLiftSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedNumericCarrier NumberedNumericDecoding NumberedNumericStep NumberedStepCertificate
open OriginalHereditaryLambda OriginalLambdaCertificate
open InternalOriginalUniformApplicationStepSelection InternalOriginalUniformParameterLeaves
open OriginalLambdaGuardLeafEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native reverse lift, retaining the original context code even when noncanonical. -/
theorem typedParentAccept (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 3)).1 = some ctx)
    (hGamma : parameterObject (v.get 0) (v.get 3) = some (Gamma,v.get 0))
    (hs : v.get 0 = packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma))
    (hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) =
      some ⟨.arrow sigma tau,.lam body⟩)
    (hm : matchingTargetValue v = 1) (hp : lamPathValue v = 1)
    (hc : leafValue n arity (childValues v) = 1) : leafValue n arity v = 1 := by
  have hg := originalGammaCode (v.get 0) (v.get 3) Gamma hGamma
  have hsb : (childValues v).get 0 =
      packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)) := by
    simp [childValues,hs,packedNumber,termCode,codeNumber,typeNumber,Nat.unpair_pair,Nat.add_comm 1]
  have hcp : (childValues v).get 3 =
      Nat.pair (Nat.unpair (v.get 3)).1 (Encodable.encode (sigma :: Gamma)) := by
    simp only [childValues,List.Vector.get_ofFn,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,hs,
      packedNumber,termCode,codeNumber,Nat.unpair_pair]
    rw [← hg,OriginalContextExtensionCalibrationProof.contextEncoding]
  have ho : parameterObject ((childValues v).get 0) ((childValues v).get 3) =
      some (sigma :: Gamma,(childValues v).get 0) := by
    rw [hcp]
    exact encodedParameterObject ((childValues v).get 0) (Nat.unpair (v.get 3)).1 (sigma :: Gamma)
  have hctxChild : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair ((childValues v).get 3)).1 = some ctx := by
    rw [hcp,Nat.unpair_pair]
    exact hcontext
  have hchild : numericStepTest n arity ctx.1.1 ctx.1.2 (sigma :: Gamma) ctx.2
      (packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)))
      ((childValues v).get 1) (stripStep (v.get 2)) = true := by
    rw [leafAtCoordinates n arity (childValues v) ctx (sigma :: Gamma) hctxChild ho] at hc
    have hcert : (childValues v).get 2 = stripStep (v.get 2) := rfl
    simpa only [hsb,hcert,Bool.toNat_eq_one] using hc
  obtain ⟨body',ht,hlift⟩ := numericLambdaLift n arity ctx.1.1 ctx.1.2 Gamma ctx.2
    sigma tau body ((childValues v).get 1) (stripStep (v.get 2)) (by simpa only [hs] using hq) hchild
  have htarget := reconstructTarget n arity v Gamma sigma tau body body' hs hm ht
  have hcert := restoreCertificate v hp
  have hstep : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 0) (v.get 1) (v.get 2) = true := by
    rw [hs,htarget,hcert]
    exact hlift
  rw [leafAtCoordinates n arity v ctx Gamma hcontext hGamma,hstep]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftTypedProof
