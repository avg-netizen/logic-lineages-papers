module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeSelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric
open InternalRawListRecursionEvaluationProof (dropZero dropSuccessor dropCons lookupEvaluation lookupConsZero lookupConsSuccessor)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo vectorThree)
open OriginalHereditaryResultStackProgram
open OriginalClassContextAllPositionNativeSelectorsProof (frontZero frontSuccessor)
attribute [local irreducible] InternalArithmeticPrograms.addition InternalEqualityTest.predecessor
 InternalRawListRecursion.drop InternalRawListRecursion.lookup
 OriginalClassContextAllPositionObserver.front OriginalTypedArgumentObservations.reverse

theorem dropNumbers (index : Nat) (xs : List Nat) :
 evaluate InternalRawListRecursion.drop (index ::ᵥ numbersNumber xs ::ᵥ nil) = numbersNumber (xs.drop index) := by
 induction index generalizing xs with
 | zero => simp only [dropZero,List.drop_zero]
 | succ index ih =>
   cases xs with
   | nil =>
     rw [dropSuccessor,ih]
     simp [numbersNumber]
   | cons head tail =>
     simp only [numbersNumber,dropCons,List.drop_succ_cons]
     exact ih tail

theorem lookupNumbers (index : Nat) (xs : List Nat) :
 evaluate InternalRawListRecursion.lookup (index ::ᵥ numbersNumber xs ::ᵥ nil) = xs.getD index 0 := by
 induction xs generalizing index with
 | nil => rw [lookupEvaluation,dropNumbers]; simp [numbersNumber]
 | cons head tail ih =>
   cases index with
   | zero => simpa [numbersNumber] using lookupConsZero head (numbersNumber tail)
   | succ index => simpa [numbersNumber,lookupConsSuccessor] using ih index

theorem frontPrefix (front suffix : List Nat) :
 evaluate OriginalClassContextAllPositionObserver.front (ofFn ![front.length,numbersNumber (front ++ suffix)]) = numbersNumber front := by
 induction front using List.reverseRecOn generalizing suffix with
 | nil => exact frontZero _
 | append_singleton front value ih =>
   simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append]
   rw [frontSuccessor,ih (value :: suffix)]
   have hl : evaluate InternalRawListRecursion.lookup (ofFn ![front.length,numbersNumber (front ++ value :: suffix)]) = value := by
     rw [vectorTwo]
     change evaluate InternalRawListRecursion.lookup (front.length ::ᵥ numbersNumber (front ++ value :: suffix) ::ᵥ nil) = value
     rw [lookupNumbers]
     simpa using OriginalHereditaryResultStackProof.getAfterPrefix front (value :: suffix) 0
   rw [hl]
   have hc : evaluate InternalListCodec.consCode (ofFn ![value,0]) = numbersNumber [value] := by
     rw [vectorTwo,InternalListCodecEvaluationProof.consEvaluation]
     rfl
   rw [hc,vectorTwo]
   exact OriginalContextInsertionCalibrationProof.appendNumbers front [value]

theorem totalEvaluation (a d code : Nat) : evaluate totalCount (a ::ᵥ d ::ᵥ code ::ᵥ nil) = d+a := by
 change evaluate InternalArithmeticPrograms.addition (ofFn ![d,a]) = _
 rw [vectorTwo]
 exact InternalArithmeticProgramsEvaluationProof.exactAdditionEvaluation d a

theorem firstIndexEvaluation (a d code : Nat) : evaluate firstIndex (a ::ᵥ d ::ᵥ code ::ᵥ nil) = (d+a).pred := by
 change evaluate InternalEqualityTest.predecessor (ofFn fun _ : Fin 1 => evaluate totalCount _) = _
 rw [vectorOne,totalEvaluation]
 exact InternalEqualityTestEvaluationProof.exactPredecessorEvaluation _

theorem firstEvaluation (a d : Nat) (xs : List Nat) :
 evaluate firstSlot (a ::ᵥ d ::ᵥ numbersNumber xs ::ᵥ nil) =
   if a=0 then 0 else xs.getD (d+a-1) 0 := by
 rw [firstSlot,InternalAcceptanceCalibrationProof.evalBranch]
 change (if a=0 then evaluate (OriginalRawSyntaxTransport.constant 3 0) _ else
   evaluate InternalRawListRecursion.lookup (ofFn ![evaluate firstIndex _,numbersNumber xs])) = _
 rw [OriginalRawSyntaxTransportEvaluationSupportProof.constantEvaluation,vectorTwo,firstIndexEvaluation]
 change (if a=0 then 0 else evaluate InternalRawListRecursion.lookup ((d+a).pred ::ᵥ numbersNumber xs ::ᵥ nil)) = _
 rw [lookupNumbers]
 rfl

theorem secondEvaluation (a d : Nat) (xs : List Nat) :
 evaluate secondSlot (a ::ᵥ d ::ᵥ numbersNumber xs ::ᵥ nil) =
   if a=2 then xs.getD d 0 else 0 := by
 rw [secondSlot,OriginalTypedDecoderEvaluationSupportProof.ifSameEvaluation]
 simp only [OriginalRawSyntaxTransportEvaluationSupportProof.constantEvaluation]
 change (if a=2 then evaluate InternalRawListRecursion.lookup (ofFn ![d,numbersNumber xs]) else 0) = _
 rw [vectorTwo]
 change (if a=2 then evaluate InternalRawListRecursion.lookup (d ::ᵥ numbersNumber xs ::ᵥ nil) else 0) = _
 rw [lookupNumbers]

theorem deletionEvaluation (children deletions old : List Nat) :
 evaluate deletionRow (children.length ::ᵥ deletions.length ::ᵥ numbersNumber (OriginalHereditaryResultStack.stack children deletions old) ::ᵥ nil) = numbersNumber deletions := by
 change evaluate OriginalTypedArgumentObservations.reverse (ofFn fun _ : Fin 1 => evaluate deletionFront _) = _
 rw [vectorOne]
 have hf : evaluate deletionFront (children.length ::ᵥ deletions.length ::ᵥ numbersNumber (OriginalHereditaryResultStack.stack children deletions old) ::ᵥ nil) = numbersNumber deletions.reverse := by
   change evaluate OriginalClassContextAllPositionObserver.front (ofFn ![deletions.length,numbersNumber (OriginalHereditaryResultStack.stack children deletions old)]) = _
   simpa only [OriginalHereditaryResultStack.stack,List.length_reverse,List.append_assoc] using frontPrefix deletions.reverse (children.reverse ++ old)
 rw [hf]
 simpa only [List.reverse_reverse] using OriginalTypedArgumentObservationsReverseProof.nativeReverse deletions.reverse

theorem oldEvaluation (children deletions old : List Nat) :
 evaluate oldSuffix (children.length ::ᵥ deletions.length ::ᵥ numbersNumber (OriginalHereditaryResultStack.stack children deletions old) ::ᵥ nil) = numbersNumber old := by
 change evaluate InternalRawListRecursion.drop (ofFn ![evaluate totalCount _,numbersNumber (OriginalHereditaryResultStack.stack children deletions old)]) = _
 rw [vectorTwo,totalEvaluation]
 change evaluate InternalRawListRecursion.drop ((deletions.length+children.length) ::ᵥ numbersNumber (OriginalHereditaryResultStack.stack children deletions old) ::ᵥ nil) = _
 rw [dropNumbers,OriginalHereditaryResultStackProof.restoreOld]

theorem calibration : OriginalHereditaryResultStackProgramTargets.Calibration := by
 intro children deletions old hb
 dsimp only
 simp only [vectorThree,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ]
 change evaluate firstSlot (children.length ::ᵥ deletions.length ::ᵥ numbersNumber (OriginalHereditaryResultStack.stack children deletions old) ::ᵥ nil) = _ ∧ _
 rw [firstEvaluation,secondEvaluation,deletionEvaluation,oldEvaluation]
 have hs := OriginalHereditaryResultStackProof.childSlots children deletions old hb
 exact ⟨congrArg Prod.fst hs,congrArg Prod.snd hs,rfl,rfl⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramProof
