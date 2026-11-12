module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftSupportProof
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
    have hc : (childValues v).get 2 = stripStep (v.get 2) := rfl
    simpa only [hc] using h
  conv_lhs => rw [← Nat.pair_unpair (v.get 2)]
  rw [hpath]
  have hz : Nat.pair 0 0 = 0 := rfl
  simp only [liftStep,positionNumber,stripStep,Nat.unpair_pair,hz]

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
  simp only [packedNumber,childValues,List.Vector.get_ofFn,Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons,
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


/-- Opaque coordinates prevent expansion of the context codec at a large child vector. -/
theorem encodedParameterObject (value context : Nat) (Gamma : List Ty) :
    parameterObject value (Nat.pair context (Encodable.encode Gamma)) = some (Gamma,value) := by
  unfold parameterObject
  rw [Nat.unpair_pair]
  exact Encodable.encodek (Gamma,value)

theorem leafAtCoordinates (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 3)).1 = some ctx)
    (hGamma : parameterObject (v.get 0) (v.get 3) = some (Gamma,v.get 0)) :
    leafValue n arity v =
      (numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2 (v.get 0) (v.get 1) (v.get 2)).toNat := by
  simp only [leafValue,hcontext,hGamma]

theorem sourceLambdaTag (v : List.Vector Nat 4)
    (hl : evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1) :
    (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 := by
  rw [OriginalLambdaGuardLeafRawProof.sourceLambdaEvaluation] at hl
  split at hl
  · assumption
  · exact False.elim (Nat.zero_ne_one hl)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeLiftSupportProof
