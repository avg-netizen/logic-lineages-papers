module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.NativeProof
open Source InternalOriginalUniformParameterLeaves NumberedUniformPackedDecoding
open TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] Primrec
theorem candidatesPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : (OrdinaryArithmeticQuotient.Context n × ContextUniform.Object) × RawPacked n =>
      ContextUniformPrimary.candidates arity p.1.1.1.1 p.1.1.1.2 p.1.2.1 p.2) :=
  (ContextUniformPrimaryPrimitiveProof.candidatesPrimitive n arity).comp
    ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))

theorem candidatesValuePrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (candidatesValue n arity) := by
  apply InternalOriginalUniformParameterLeavesPrimitiveProof.decodedValuePrimitive n
    (fun p => ((rawPackedDecode n arity p.2.1 p.2.2).map
      (fun q => Membership.entriesCode (ContextUniformPrimary.candidates arity p.1.1.1 p.1.1.2 p.2.1 q))).getD 0)
  have hd : Primrec (fun p : OrdinaryArithmeticQuotient.Context n × ContextUniform.Object =>
      rawPackedDecode n arity p.2.1 p.2.2) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp Primrec.snd
  have hv := MembershipLeafSelectionProof.entriesPrimitive _ (candidatesPrimitive n arity)
  exact Primrec.option_getD.comp (Primrec.option_map hd hv.to₂) (Primrec.const 0)


theorem consEntries {n : Nat} (q : RawPacked n) (xs : List (RawPacked n)) :
    evaluate InternalListCodec.consCode (List.Vector.ofFn ![Encodable.encode q,Membership.entriesCode xs]) =
      Membership.entriesCode (q :: xs) := by
  simpa only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,
    Matrix.cons_val_one,Membership.entriesCode,List.map_cons,NumberedMultisetNumeric.numbersNumber] using
    (InternalListCodecEvaluationProof.consEvaluation (Encodable.encode q) (Membership.entriesCode xs))

theorem poolCalibration (n : Nat) (arity : Fin n → Nat) (T Q : Program 2)
    (hT : ∀ v, evaluate T v = targetValue n arity v)
    (hQ : ∀ v, evaluate Q v = candidatesValue n arity v) :
    ∀ v, evaluate (pool T Q) v = TransparentPrimary.poolValue n arity v := by
  intro v
  rw [pool,InternalAcceptanceCalibrationProof.evalBranch,hT]
  change (if targetValue n arity v = 0 then 0 else
    evaluate InternalListCodec.consCode (List.Vector.ofFn ![v.get 0,evaluate Q v])) = _
  rw [hQ]
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma (v.get 1)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1 with
  | none => simp only [targetValue,candidatesValue,TransparentPrimary.poolValue,decodedValue,hc,if_pos rfl]
  | some ctx =>
    cases hd : rawPackedDecode n arity Gamma (v.get 0) with
    | none => simp only [targetValue,candidatesValue,TransparentPrimary.poolValue,decodedValue,hc,
        ho (v.get 0),hd,Option.isSome_none,Bool.toNat_false,Option.map_none,Option.getD_none,if_pos rfl]
    | some q =>
      have he := TransparentCandidate.NativeProof.rawReencoding n arity Gamma (v.get 0)
      simp only [hd,Option.map_some,Option.getD_some,Option.isSome_some,Bool.toNat_true,ite_true] at he
      simp only [targetValue,candidatesValue,TransparentPrimary.poolValue,decodedValue,hc,
        ho (v.get 0),hd,Option.isSome_some,Bool.toNat_true,Option.map_some,Option.getD_some,
        Nat.one_ne_zero,if_false,ContextUniformPrimary.vertices]
      rw [← he]
      exact consEntries q (ContextUniformPrimary.candidates arity ctx.1.1 ctx.1.2 Gamma q)

theorem selectedTuple : Targets.SelectedTuple := by
  intro n arity p H G W hp hH hG hW
  obtain ⟨Q,hQ⟩ := Proof.allPrimitiveFunctions 2 _ (candidatesValuePrimitive n arity)
  obtain ⟨C,P,E,hC,hP,hE⟩ := TransparentPrimary.SelectionProof.supplierSelection n arity
  let T := OriginalTypedDecoder.target H G
  have hT := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hPool := poolCalibration n arity T Q hT hQ
  have hs : TransparentPrimary.SuppliersCalibrated n arity
      (LengthAlignedPrimary.countOfPool (pool T Q)) (pool T Q) E :=
    ⟨LengthAlignedPrimary.NativeProof.countCalibration n arity (pool T Q) hPool,hPool,hE⟩
  have hL := TransparentPrimary.NativeProof.calibration n arity T
    (LengthAlignedPrimary.countOfPool (pool T Q)) (pool T Q) E hT hs
  have hr := CandidateIntegration.Proof.retainedTuple n arity p H G W
    (primary T Q E) hp hH hG hW hL
  exact ⟨Q,E,hQ,hs,hL,hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.NativeProof
