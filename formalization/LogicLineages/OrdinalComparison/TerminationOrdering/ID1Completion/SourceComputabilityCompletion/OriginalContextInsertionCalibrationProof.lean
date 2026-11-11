module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
open Source NumberedLeastCodeRepresentative NumberedMultisetNumeric
open NumberedMultisetNumericSupportProof NumberedMultisetNumericTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalContextInsertion OriginalContextExtensionCalibrationProof
open InternalRawListRecursionEvaluationProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)

/-- Original Encodable contexts are original number lists of original type
numbers. This does not identify them with the separate typesNumber codec. -/
theorem contextNumbers (Gamma : List Ty) :
    Encodable.encode Gamma = numbersNumber (Gamma.map typeNumber) := by
  induction Gamma with
  | nil => rfl
  | cons sigma Gamma ih =>
    simp only [contextEncoding,List.map_cons,numbersNumber,ih]
    omega

theorem lengthNumbers (xs : List Nat) :
    evaluate length (numbersNumber xs ::ᵥ List.Vector.nil) = xs.length := by
  unfold OriginalContextInsertion.length
  rw [actualRawListRecursionEvaluation,numbersRoundTrip]
  change xs.foldr (fun _ n => n+1) 0 = xs.length
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons,List.length_cons,ih]

theorem appendNumbers (xs ys : List Nat) :
    evaluate InternalApplicationValidityStackAppend.append
      (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ List.Vector.nil) =
      numbersNumber (xs ++ ys) := by
  unfold InternalApplicationValidityStackAppend.append
  rw [actualRawListRecursionEvaluation,numbersRoundTrip]
  change xs.foldr (fun h t => evaluate InternalListCodec.consCode
    (List.Vector.ofFn ![h,t])) (numbersNumber ys) = numbersNumber (xs ++ ys)
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldr_cons,ih]
    simp only [List.cons_append,numbersNumber,InternalEqualityTestEvaluationProof.vectorTwo,
      Matrix.cons_val_zero,Matrix.cons_val_one,InternalListCodecEvaluationProof.consEvaluation]

 theorem lengthContext (Gamma : List Ty) :
    evaluate length (List.Vector.ofFn ![Encodable.encode Gamma]) = Gamma.length := by
  simp only [vectorOne,Matrix.cons_val_zero,contextNumbers,lengthNumbers,List.length_map]

 theorem appendContext (front suffix : List Ty) :
    evaluate InternalApplicationValidityStackAppend.append
      (List.Vector.ofFn ![Encodable.encode front,Encodable.encode suffix]) =
      Encodable.encode (front ++ suffix) := by
  simp only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one,contextNumbers,
    appendNumbers,List.map_append]

/-- Every raw number is an original Encodable Ty context. This is native
calibration only, independent from the internal list-code induction. -/
 theorem contextSurjective (code : Nat) : ∃ Gamma : List Ty, Encodable.encode Gamma = code := by
  obtain ⟨xs,hxs⟩ := encodingSurjective code
  refine ⟨xs.map NumberedTypeCodecPrimrec.typeEquiv.symm, ?_⟩
  rw [contextNumbers,List.map_map]
  have he : (typeNumber ∘ NumberedTypeCodecPrimrec.typeEquiv.symm) = id := by
    funext n
    exact NumberedTypeCodecPrimrec.typeEquiv.apply_symm_apply n
  rw [he,List.map_id,hxs]

 theorem actualOriginalContextInsertionListCalibration :
    OriginalContextInsertionTargets.ActualOriginalContextInsertionListCalibration :=
  ⟨lengthContext,appendContext⟩

 theorem actualOriginalContextInsertionCalibration :
    OriginalContextInsertionTargets.ActualOriginalContextInsertionCalibration := by
  intro d cutoff Gamma extended
  constructor
  · rintro ⟨front,suffix,inserted,hlen,hfront,hcons,hext⟩
    obtain ⟨P,hP⟩ := contextSurjective front
    obtain ⟨S,hS⟩ := contextSurjective suffix
    have hd : Encodable.encode (d :: S) = inserted := by
      rw [← hS] at hcons
      rw [actualOriginalContextConsCalibration] at hcons
      exact hcons
    refine ⟨P,S,?_,?_,?_⟩
    · apply Encodable.encode_injective
      rw [← hP,← hS,appendContext] at hfront
      exact hfront.symm
    · apply Encodable.encode_injective
      rw [← hP,← hd,appendContext] at hext
      exact hext.symm
    · rw [← hP,lengthContext] at hlen
      exact hlen
  · rintro ⟨P,S,rfl,rfl,hP⟩
    exact ⟨Encodable.encode P,Encodable.encode S,Encodable.encode (d :: S),
      (lengthContext P).trans hP,appendContext P S,
      actualOriginalContextConsCalibration d S,appendContext P (d :: S)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
