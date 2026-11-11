module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalHereditaryLambda OriginalHereditaryLambdaRawProof OriginalHereditaryLambdaControlProof
open InternalOriginalUniformApplicationStepSelection
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem activeFacts (v : List.Vector Nat 4) (h : stopValue v = 0) :
    evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1 ∧
      evaluate OriginalLambdaGuardLeaf.sameBottom v = 0 := by
  rw [OriginalLambdaGuardLeafRawProof.sourceLambdaEvaluation,
    OriginalLambdaGuardLeafEvaluationSupportProof.sameBottomEvaluation]
  by_cases hl : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 <;>
    by_cases hb : v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1
      (Nat.pair 3 (Nat.unpair (v.get 0)).1) <;>
        simp only [stopValue,hl,hb,ite_true,ite_false] at h ⊢ <;> simp_all

theorem lamPathOfRestore (v : List.Vector Nat 4)
    (h : v.get 2 = OriginalLambdaCertificate.liftStep
      (OriginalLambdaCertificate.stripStep (v.get 2))) : lamPathValue v = 1 := by
  have hzero : Nat.pair 0 0 = 0 := rfl
  have hp : (Nat.unpair (v.get 2)).1 =
      1 + Nat.pair 0 (Nat.unpair (OriginalLambdaCertificate.stripStep (v.get 2))).1 := by
    simpa only [OriginalLambdaCertificate.liftStep,NumberedNumericStep.positionNumber,
      Nat.unpair_pair,hzero] using congrArg (fun code : Nat => (Nat.unpair code).1) h
  unfold lamPathValue
  rw [hp]
  simp [Nat.add_comm 1,Nat.unpair_pair]

/-- SAME-certificate numeric inversion supplies the original path prefix;
the already checked one-level guard theorem alone did not retain this fact. -/
theorem typedLambdaLamPath (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (hs : v.get 0 = packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma))
    (hstep : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 0) (v.get 1) (v.get 2) = true)
    (hnotbottom : evaluate OriginalLambdaGuardLeaf.sameBottom v ≠ 1) :
    lamPathValue v = 1 := by
  have hn : v.get 1 ≠ packedNumber
      (⟨.arrow sigma tau,.bottom (.arrow sigma tau)⟩ : Packed (Fin n) arity Gamma) := by
    intro he
    apply hnotbottom
    rw [OriginalLambdaGuardLeafEvaluationSupportProof.sameBottomEvaluation]
    simp [hs,he,packedNumber,termCode,codeNumber,Nat.unpair_pair]
  obtain ⟨_,body',decoded,rest,_,_,_,_,_,hrestore,_,_⟩ :=
    OriginalLambdaCertificateProof.actualNumericLambdaCertificateNonbottomInversion
      n arity ctx.1.1 ctx.1.2 Gamma ctx.2 sigma tau body (v.get 1) (v.get 2)
      hn (by simpa only [hs] using hstep)
  exact lamPathOfRestore v hrestore

/-- Decode the accepted original source and SAME supplied certificate only.
The original context code is never replaced by a preferred representative. -/
theorem leafLamPath (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (ha : leafValue n arity v = 1)
    (hlambda : evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1)
    (hnotbottom : evaluate OriginalLambdaGuardLeaf.sameBottom v ≠ 1) :
    lamPathValue v = 1 := by
  have htag : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 := by
    rw [OriginalLambdaGuardLeafRawProof.sourceLambdaEvaluation] at hlambda
    split at hlambda
    · assumption
    · contradiction
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (v.get 3)
  cases hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 3)).1 with
  | none => simp [leafValue,hcontext] at ha
  | some ctx =>
    have hstep : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) = true := by
      cases hstep : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) <;> simp_all [leafValue]
    obtain ⟨tau,q,r,_,_,hs,_⟩ :=
      (NumberedNumericStepProof.numericStepCertificates n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1)).mp ⟨v.get 2,hstep⟩
    rw [← hs] at htag
    cases q
    case lam =>
      exact typedLambdaLamPath n arity v ctx Gamma _ _ _ hs.symm hstep hnotbottom
    all_goals simp [packedNumber,termCode,codeNumber] at htag

theorem leafActiveAdvance (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hcal : LeafCalibrated n arity oldStep) (v : List.Vector Nat 4)
    (ha : leafValue n arity v = 1) (hs : stopValue v = 0) :
    matchingTargetValue v = 1 ∧ lamPathValue v = 1 ∧ evaluate oldStep (childValues v) = 1 := by
  obtain ⟨hlambda,hbottom⟩ := activeFacts v hs
  have hn : evaluate OriginalLambdaGuardLeaf.sameBottom v ≠ 1 := by
    rw [hbottom]
    decide
  have hg := OriginalLambdaGuardLeafEvaluationProof.leafChildAccept n arity oldStep hcal v
    ha hlambda hn
  rw [OriginalLambdaGuardLeaf.childGuard,conjunctionEvaluation] at hg
  have hparts : evaluate OriginalLambdaGuardLeaf.matchingTarget v = 1 ∧
      evaluate (OriginalLambdaGuardLeaf.childCheck oldStep) v = 1 := by
    split at hg
    · assumption
    · contradiction
  rw [matchingTargetEvaluation,childCheckEvaluation] at hparts
  exact ⟨hparts.1,leafLamPath n arity v ha hlambda hn,hparts.2⟩

theorem childPathValue (v : List.Vector Nat 4) :
    (Nat.unpair ((childValues v).get 2)).1 =
      (Nat.unpair ((Nat.unpair (v.get 2)).1 - 1)).2 := by
  simp [childValues,OriginalLambdaCertificate.stripStep,Nat.unpair_pair]

theorem lamPathCode (v : List.Vector Nat 4) (h : lamPathValue v = 1) :
    (Nat.unpair (v.get 2)).1 =
      1 + Nat.pair 0 (Nat.unpair ((childValues v).get 2)).1 := by
  have hp : (Nat.unpair (v.get 2)).1 ≠ 0 ∧
      (Nat.unpair ((Nat.unpair (v.get 2)).1 - 1)).1 = 0 := by
    dsimp only [lamPathValue] at h
    split at h
    · assumption
    · contradiction
  rw [childPathValue,← hp.2,Nat.pair_unpair]
  omega

theorem childPathLt (v : List.Vector Nat 4) (h : lamPathValue v = 1) :
    (Nat.unpair ((childValues v).get 2)).1 < (Nat.unpair (v.get 2)).1 := by
  have hc := lamPathCode v h
  have hb := Nat.unpair_right_le
    (Nat.pair 0 (Nat.unpair ((childValues v).get 2)).1)
  rw [Nat.unpair_pair] at hb
  omega

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
