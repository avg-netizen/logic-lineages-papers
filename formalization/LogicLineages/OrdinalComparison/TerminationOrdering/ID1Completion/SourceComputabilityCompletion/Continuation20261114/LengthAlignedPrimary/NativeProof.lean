module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.NativeProof
open Source InternalOriginalUniformParameterLeaves
open TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem lengthZero : evaluate OriginalContextInsertion.length (List.Vector.ofFn ![0]) = 0 :=
  OriginalContextInsertionCalibrationProof.lengthNumbers []

theorem lengthEntries {n : Nat} (xs : List (NumberedUniformPackedDecoding.RawPacked n)) :
    evaluate OriginalContextInsertion.length (List.Vector.ofFn ![Membership.entriesCode xs]) = xs.length := by
  have h := OriginalContextInsertionCalibrationProof.lengthNumbers (xs.map Encodable.encode)
  simpa only [Membership.entriesCode,InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero,List.length_map] using h

theorem poolLengthValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) :
    evaluate OriginalContextInsertion.length (List.Vector.ofFn ![TransparentPrimary.poolValue n arity v]) =
      TransparentPrimary.countValue n arity v := by
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1 with
  | none =>
    simpa only [TransparentPrimary.poolValue,TransparentPrimary.countValue,decodedValue,hc] using lengthZero
  | some ctx =>
    cases ho : parameterObject (v.get 0) (v.get 1) with
    | none =>
      simpa only [TransparentPrimary.poolValue,TransparentPrimary.countValue,decodedValue,hc,ho] using lengthZero
    | some obj =>
      cases hd : NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2 with
      | none =>
        simpa only [TransparentPrimary.poolValue,TransparentPrimary.countValue,decodedValue,hc,ho,hd,
          Option.map_none,Option.getD_none] using lengthZero
      | some q =>
        simpa only [TransparentPrimary.poolValue,TransparentPrimary.countValue,decodedValue,hc,ho,hd,
          Option.map_some,Option.getD_some] using
          (lengthEntries (ContextUniformPrimary.vertices arity ctx.1.1 ctx.1.2 obj.1 q))

theorem countCalibration (n : Nat) (arity : Fin n → Nat) (P : Program 2)
    (hP : ∀ v, evaluate P v = TransparentPrimary.poolValue n arity v) :
    ∀ v, evaluate (countOfPool P) v = TransparentPrimary.countValue n arity v := by
  intro v
  change evaluate OriginalContextInsertion.length (List.Vector.ofFn ![evaluate P v]) = _
  rw [hP]
  exact poolLengthValue n arity v

theorem supplierSelection (n : Nat) (arity : Fin n → Nat) :
    ∃ (P : Program 2) (E : Program 3),
      TransparentPrimary.SuppliersCalibrated n arity (countOfPool P) P E := by
  obtain ⟨C,P,E,hC,hP,hE⟩ := TransparentPrimary.SelectionProof.supplierSelection n arity
  exact ⟨P,E,countCalibration n arity P hP,hP,hE⟩

theorem selectedTuple : Targets.SelectedTuple := by
  intro n arity p H G W hp hH hG hW
  obtain ⟨P,E,hs⟩ := supplierSelection n arity
  have hT := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hL := TransparentPrimary.NativeProof.calibration n arity
    (OriginalTypedDecoder.target H G) (countOfPool P) P E hT hs
  have hr := CandidateIntegration.Proof.retainedTuple n arity p H G W
    (primary (OriginalTypedDecoder.target H G) P E) hp hH hG hW hL
  exact ⟨P,E,hs,hL,hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.NativeProof
