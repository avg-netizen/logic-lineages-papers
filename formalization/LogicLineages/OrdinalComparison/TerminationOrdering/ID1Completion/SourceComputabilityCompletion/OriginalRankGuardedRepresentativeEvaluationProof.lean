module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalStepGuard (sourceValidityValue)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open BottomRepresentativeEvaluationProof (parameterGamma decodedLeafSlice windowAtEvaluation)
open OriginalRawObjectTransportEvaluationProof (rankPackedEvaluation)
open OriginalRawSyntaxTransport OriginalRankGuardedRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Native rank calibration for the ORIGINAL packed encoding. -/
theorem packedRank (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) :
    evaluate variableRankPackedRaw (ofFn ![packedNumber q]) =
      NumberedVariableCount.packedVariableCount q := by
  obtain ⟨tau,q⟩ := q
  rw [rankPackedEvaluation]
  simp only [packedNumber,Nat.unpair_pair]
  exact (OriginalRawSyntaxTransportTypedProof.actualRawSyntaxTypedCalibration
    n arity [] Gamma Ty.ground tau).2.2 q

/-- The existing primary-equivalence theorem pays the actual rank check.
Its closure and source-universe assumptions come from the two active guards. -/
theorem representativeRank (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (q : Packed (Fin n) arity Gamma) (hq : InUniverse symbols S q.2) :
    evaluate variableRankPackedRaw (ofFn ![representativeCode symbols S q]) =
      evaluate variableRankPackedRaw (ofFn ![packedNumber q]) := by
  obtain ⟨r,hr,he⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
    n arity symbols S hS Gamma q hq
  rw [he,packedRank,packedRank]
  exact (NumberedVariableCountProof.actualPrimaryVariableCount
    (Fin n) arity symbols S Gamma q r hr).symm

theorem validRepresentativeRank (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S)) (value : Nat)
    (hv : sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate variableRankPackedRaw
      (ofFn ![targetRepresentativeValue n arity symbols S Gamma value]) =
      evaluate variableRankPackedRaw (ofFn ![value]) := by
  cases hd : decodeUniverse n arity symbols S Gamma value with
  | none => simp [sourceValidityValue,rawCarrierTest,hd] at hv
  | some q =>
    obtain ⟨hn,hq⟩ :=
      (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value q).mp hd
    have hp := (Option.filter_eq_some_iff.mp hd).1
    rw [targetRepresentativeValue,hp,← hn]
    exact representativeRank n arity symbols S Gamma hS q hq

theorem sameRankEvaluation (R : Program 2) (value parameter : Nat) :
    evaluate (sameRank R) (ofFn ![value,parameter]) =
      if evaluate variableRankPackedRaw (ofFn ![evaluate R (ofFn ![value,parameter])]) =
          evaluate variableRankPackedRaw (ofFn ![value]) then 1 else 0 := by
  rw [sameRank,sameEvaluation]
  change (if evaluate variableRankPackedRaw
      (ofFn fun _ : Fin 1 => evaluate R (ofFn ![value,parameter])) =
    evaluate variableRankPackedRaw (ofFn fun _ : Fin 1 => value) then 1 else 0) = _
  simp only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero]

/-- All vectors, including arbitrary malformed contexts and nonclosed windows.
Inactive vectors keep R literally; active vectors decode the SAME source/context. -/
theorem representativeUnchanged (n : Nat) (arity : Fin n → Nat)
    (data : Data) (window : Program 1) (hc : Calibrated n arity data)
    (hw : ∀ v, evaluate window v = GuardCalibration.validWindowValue n v)
    (v : List.Vector Nat 2) :
    evaluate (representative data.oldSource data.oldRepresentative window) v =
      evaluate data.oldRepresentative v := by
  have hv : v = ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  rw [hv,OriginalRankGuardedRepresentative.representative,evalBranch]
  by_cases ha : evaluate (active data.oldSource window) (ofFn ![v.get 0,v.get 1]) = 0
  · simp only [ha,ite_true]
  · simp only [ha,ite_false]
    have hactive : evaluate (BottomRepresentative.windowAt window) (ofFn ![v.get 0,v.get 1]) = 1 ∧
        evaluate data.oldSource (ofFn ![v.get 0,v.get 1]) = 1 := by
      by_contra h
      apply ha
      rw [active,conjunctionEvaluation]
      exact if_neg h
    have hwindow : GuardCalibration.validWindow n (Nat.unpair (v.get 1)).1 = 1 := by
      simpa only [windowAtEvaluation,hw,GuardCalibration.validWindowValue,
        List.Vector.get_ofFn,Matrix.cons_val_zero] using hactive.1
    obtain ⟨ctx,hctx,hclosed⟩ :=
      (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 1)).1).1.mp hwindow
    obtain ⟨Gamma,ho⟩ := parameterGamma (v.get 1)
    have hslice := decodedLeafSlice n arity data hc (v.get 1) ctx hctx Gamma ho (v.get 0)
    have he : evaluate variableRankPackedRaw
        (ofFn ![evaluate data.oldRepresentative (ofFn ![v.get 0,v.get 1])]) =
        evaluate variableRankPackedRaw (ofFn ![v.get 0]) := by
      rw [hslice.2.2.1]
      exact validRepresentativeRank n arity ctx.1.1 ctx.1.2 Gamma hclosed (v.get 0)
        (hslice.1.symm.trans hactive.2)
    rw [evalBranch,sameRankEvaluation]
    simp only [he,ite_true,Nat.one_ne_zero,ite_false]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeEvaluationProof
