module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalLambdaGuardLeaf OriginalLambdaGuardLeafRawProof
open InternalOriginalUniformApplicationStepSelection
open InternalOriginalUniformParameterLeaves (parameterObject)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem targetDomainEvaluation (v : List.Vector Nat 4) :
    evaluate (.composition OriginalLambdaConstructor.domain
      (fun _ : Fin 1 => Program.projection 1)) v =
      (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).1 := by
  change evaluate OriginalLambdaConstructor.domain
    (List.Vector.ofFn fun _ : Fin 1 => v.get 1) = _
  rw [OriginalLambdaConstructorEvaluationProof.domainEvaluation]
  rfl

theorem sameBottomEvaluation (v : List.Vector Nat 4) :
    evaluate sameBottom v =
      if v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1
        (Nat.pair 3 (Nat.unpair (v.get 0)).1) then 1 else 0 := by
  rw [sameBottom,sameEvaluation,OriginalConstructorLeafEvaluationProof.expectedBottomEvaluation]
  rfl

theorem childCheckEvaluation (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (childCheck oldStep) v = evaluate oldStep (List.Vector.ofFn
      ![evaluate sourceBody v,evaluate targetBody v,
        evaluate childCertificate v,evaluate childParameter v]) := by
  change evaluate oldStep (List.Vector.ofFn fun i : Fin 4 =>
    evaluate ((![sourceBody,targetBody,childCertificate,childParameter] : Fin 4 → Program 4) i) v) = _
  rfl

/-- Recover only the original Gamma encoding. The context's raw code is NOT
replaced by a preferred encoding of its decoded value. -/
theorem originalGammaCode (value parameter : Nat) (Gamma : List Ty)
    (h : parameterObject value parameter = some (Gamma,value)) :
    Encodable.encode Gamma = (Nat.unpair parameter).2 := by
  have he := (JointGammaDomainCodecProof.actualObjectCodec.2.1
    (Nat.pair (Nat.unpair parameter).2 value) (Gamma,value)).mp h
  have hl := congrArg (fun k : Nat => (Nat.unpair k).1) he
  simpa only [ContextUniform.objectCode,Encodable.encode_prod_val,
    Encodable.encode_nat,Nat.unpair_pair] using hl

/-- This uses the SAME successful numeric certificate and the accepted
checker-level lambda inversion. No completeness-selected child certificate
replaces it. The outer context code is retained even when noncanonical. -/
theorem typedLambdaChildAccept (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hcal : LeafCalibrated n arity oldStep) (v : List.Vector Nat 4)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 3)).1 = some ctx)
    (hGamma : Encodable.encode Gamma = (Nat.unpair (v.get 3)).2)
    (hs : v.get 0 = packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma))
    (hstep : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 0) (v.get 1) (v.get 2) = true)
    (hnotbottom : evaluate sameBottom v ≠ 1) :
    evaluate (childGuard oldStep) v = 1 := by
  have hn : v.get 1 ≠ packedNumber
      (⟨.arrow sigma tau,.bottom (.arrow sigma tau)⟩ : Packed (Fin n) arity Gamma) := by
    intro he
    apply hnotbottom
    rw [sameBottomEvaluation]
    simp [hs,he,packedNumber,termCode,codeNumber,Nat.unpair_pair]
  obtain ⟨_,body',decoded,rest,_,_,hr,_,_,_,_,hchild⟩ :=
    OriginalLambdaCertificateProof.actualNumericLambdaCertificateNonbottomInversion
      n arity ctx.1.1 ctx.1.2 Gamma ctx.2 sigma tau body (v.get 1) (v.get 2)
      hn (by simpa only [hs] using hstep)
  have hm : evaluate matchingTarget v = 1 := by
    simp [matchingTarget,conjunctionEvaluation,targetLambdaEvaluation,sameEvaluation,
      leftOfEvaluation,projectionEvaluation,sourceDomainEvaluation,targetDomainEvaluation,
      hs,hr,packedNumber,termCode,codeNumber,Nat.unpair_pair]
  have hsb : evaluate sourceBody v =
      packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)) := by
    rw [sourceBodyEvaluation,hs]
    simp [packedNumber,termCode,codeNumber,typeNumber,Nat.unpair_pair,Nat.add_comm 1]
  have htb : evaluate targetBody v =
      packedNumber (⟨tau,body'⟩ : Packed (Fin n) arity (sigma :: Gamma)) := by
    rw [targetBodyEvaluation,hs,hr]
    simp [packedNumber,termCode,codeNumber,typeNumber,Nat.unpair_pair,Nat.add_comm 1]
  have hp : evaluate childParameter v =
      Nat.pair (Nat.unpair (v.get 3)).1 (Encodable.encode (sigma :: Gamma)) := by
    rw [childParameterEvaluation,hs]
    simp only [packedNumber,termCode,codeNumber,Nat.unpair_pair]
    rw [← hGamma,OriginalContextExtensionCalibrationProof.contextEncoding]
  have ho : parameterObject
      (packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)))
      (Nat.pair (Nat.unpair (v.get 3)).1 (Encodable.encode (sigma :: Gamma))) =
        some (sigma :: Gamma,
          packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma))) := by
    unfold parameterObject
    rw [Nat.unpair_pair]
    exact Encodable.encodek (sigma :: Gamma,
      packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)))
  have hc : evaluate (childCheck oldStep) v = 1 := by
    rw [childCheckEvaluation,hsb,htb,childCertificateEvaluation,hp,hcal]
    simp only [leafValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
      Nat.unpair_pair,hcontext,ho,hchild,Bool.toNat_true]
  simp only [childGuard,conjunctionEvaluation,hm,hc,ite_true,and_self]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationSupportProof
