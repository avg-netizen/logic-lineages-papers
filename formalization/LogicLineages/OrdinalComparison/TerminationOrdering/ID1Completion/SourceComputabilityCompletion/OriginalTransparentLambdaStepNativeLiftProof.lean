module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedNumericCarrier NumberedNumericDecoding NumberedNumericStep NumberedStepCertificate
open OriginalHereditaryLambda OriginalLambdaCertificate
open InternalOriginalUniformApplicationStepSelection InternalOriginalUniformParameterLeaves
open OriginalLambdaGuardLeafEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Recover the original supplied certificate, not a completeness-selected witness. -/
theorem restoreCertificate (v : List.Vector Nat 4) (hp : lamPathValue v = 1) :
    v.get 2 = liftStep (stripStep (v.get 2)) := by
  have h := OriginalHereditaryLambdaEvaluationSupportProof.lamPathCode v hp
  have hpath : (Nat.unpair (v.get 2)).1 =
      1 + Nat.pair 0 (Nat.unpair (stripStep (v.get 2))).1 := by
    simpa only [childValues,List.Vector.get_ofFn,Matrix.cons_val_two] using h
  conv_lhs => rw [← Nat.pair_unpair (v.get 2)]
  rw [hpath]
  simp only [liftStep,positionNumber,stripStep,Nat.unpair_pair]

/-- Lift the SAME decoded numeric certificate under the original lambda. -/
theorem numericLambdaLift (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau) (target certificate : Nat)
    (hq : decodeUniverse n arity symbols S Gamma
      (packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma)) =
        some ⟨.arrow sigma tau,.lam body⟩)
    (hc : numericStepTest n arity symbols S (sigma :: Gamma) table
      (packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma))) target certificate = true) :
    ∃ body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
      packedNumber (⟨tau,body'⟩ : Packed (Fin n) arity (sigma :: Gamma)) = target ∧
      numericStepTest n arity symbols S Gamma table
        (packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma))
        (packedNumber (⟨.arrow sigma tau,.lam body'⟩ : Packed (Fin n) arity Gamma))
        (liftStep certificate) = true := by
  have hu := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma _ _).mp hq
  have hb : NumberedFiniteUniverse.InUniverse symbols S body := ⟨hu.2.1.2.2,hu.2.2⟩
  have hdb := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S
    (sigma :: Gamma) _ (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma))).mpr ⟨rfl,hb⟩
  cases ht : decodePackedNumber n arity (sigma :: Gamma) target with
  | none => simp only [numericStepTest,hdb,ht] at hc; contradiction
  | some r =>
    obtain ⟨rho,r⟩ := r
    cases hd : decodeStepCertificate certificate with
    | none => simp only [numericStepTest,hdb,ht,hd] at hc; contradiction
    | some c =>
      simp only [numericStepTest,hdb,ht,hd] at hc
      split at hc
      next he =>
        subst rho
        have heCode := NumberedNumericStepSupportProof.certificateSound certificate c hd
        refine ⟨r,NumberedNumericDecodingProof.packedNumericSound n arity
          (sigma :: Gamma) target _ ht,?_⟩
        rw [← heCode,OriginalLambdaCertificateCodingProof.liftStepEncoding]
        have hdr := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
          (⟨.arrow sigma tau,.lam r⟩ : Packed (Fin n) arity Gamma)
        simp only [numericStepTest,hq,hdr,
          NumberedNumericStepSupportProof.certificateRoundTrip,↓reduceDIte]
        rw [OriginalLambdaCertificateTypedProof.actualTypedLambdaCertificateLift]
        exact hc
      next => contradiction

/-- Matching raw constructor fields recover the actual parent target. -/
theorem reconstructTarget (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (Gamma : List Ty) (sigma tau : Ty)
    (body body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (hs : v.get 0 = packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma))
    (hm : matchingTargetValue v = 1)
    (ht : packedNumber (⟨tau,body'⟩ : Packed (Fin n) arity (sigma :: Gamma)) =
      (childValues v).get 1) :
    v.get 1 = packedNumber (⟨.arrow sigma tau,.lam body'⟩ : Packed (Fin n) arity Gamma) := by
  have hf : (Nat.unpair (Nat.unpair (v.get 1)).2).1 = 1 ∧
      (Nat.unpair (v.get 1)).1 = (Nat.unpair (v.get 0)).1 ∧
      (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).1 =
        (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).1 := by
    unfold matchingTargetValue at hm
    split at hm
    · assumption
    · contradiction
  have hb := congrArg (fun k : Nat => (Nat.unpair k).2) ht
  simp only [packedNumber,childValues,List.Vector.get_ofFn,Matrix.cons_val_one,
    Nat.unpair_pair] at hb
  have ht0 : (Nat.unpair (v.get 1)).1 = typeNumber (.arrow sigma tau) := by
    simpa only [hs,packedNumber,Nat.unpair_pair] using hf.2.1
  have hd : (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).1 = typeNumber sigma := by
    simpa only [hs,packedNumber,termCode,codeNumber,Nat.unpair_pair] using hf.2.2
  calc
    v.get 1 = Nat.pair (Nat.unpair (v.get 1)).1 (Nat.unpair (v.get 1)).2 := (Nat.pair_unpair _).symm
    _ = Nat.pair (typeNumber (.arrow sigma tau))
      (Nat.pair 1 (Nat.pair (typeNumber sigma) (codeNumber (termCode body')))) := by
        rw [ht0,← Nat.pair_unpair (Nat.unpair (v.get 1)).2,hf.1,
          ← Nat.pair_unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2,hd,← hb]
    _ = _ := rfl

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
    simp only [childValues,List.Vector.get_ofFn,Matrix.cons_val_three,hs,
      packedNumber,termCode,codeNumber,Nat.unpair_pair]
    rw [← hg,OriginalContextExtensionCalibrationProof.contextEncoding]
  have ho : parameterObject ((childValues v).get 0) ((childValues v).get 3) =
      some (sigma :: Gamma,(childValues v).get 0) := by
    rw [hcp]
    unfold parameterObject
    rw [Nat.unpair_pair]
    exact Encodable.encodek (sigma :: Gamma,(childValues v).get 0)
  have hchild : numericStepTest n arity ctx.1.1 ctx.1.2 (sigma :: Gamma) ctx.2
      (packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)))
      ((childValues v).get 1) (stripStep (v.get 2)) = true := by
    simp only [leafValue,ho,hcp,Nat.unpair_pair,hcontext,hsb] at hc
    have hcert : (childValues v).get 2 = stripStep (v.get 2) := rfl
    rw [hcert] at hc
    cases he : numericStepTest n arity ctx.1.1 ctx.1.2 (sigma :: Gamma) ctx.2
      (packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)))
      ((childValues v).get 1) (stripStep (v.get 2)) <;> simp_all only [Bool.toNat_false,Bool.toNat_true]
  obtain ⟨body',ht,hlift⟩ := numericLambdaLift n arity ctx.1.1 ctx.1.2 Gamma ctx.2
    sigma tau body ((childValues v).get 1) (stripStep (v.get 2)) (by simpa only [hs] using hq) hchild
  have htarget := reconstructTarget n arity v Gamma sigma tau body body' hs hm ht
  have hcert := restoreCertificate v hp
  have hstep : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 0) (v.get 1) (v.get 2) = true := by
    rw [hs,htarget,hcert]
    exact hlift
  simp only [leafValue,hcontext,hGamma,hstep,Bool.toNat_true]

/-- Exact actual-hop reverse implication. No replacement certificate or context. -/
theorem leafParentAccept (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (hs : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1)
    (hl : evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1)
    (hm : matchingTargetValue v = 1) (hp : lamPathValue v = 1)
    (hc : leafValue n arity (childValues v) = 1) : leafValue n arity v = 1 := by
  have htag : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 := by
    rw [OriginalLambdaGuardLeafRawProof.sourceLambdaEvaluation] at hl
    split at hl
    · assumption
    · contradiction
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (v.get 3)
  cases hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 3)).1 with
  | none => simp [sourceValue,decodedValue,hcontext] at hs
  | some ctx =>
    simp only [sourceValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
      decodedValue,hcontext,hGamma] at hs
    cases hq : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) with
    | none => simp [rawCarrierTest,hq] at hs
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
