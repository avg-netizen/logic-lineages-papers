module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationRootUniformityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelObservationProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedFiniteUniverse
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorFibreCountermodel
theorem rootEqual (Q : Program 2) :
 evaluate (OriginalRootObservation.rootObservation Q) (List.Vector.ofFn ![leftCode,parameter]) =
 evaluate (OriginalRootObservation.rootObservation Q) (List.Vector.ofFn ![rightCode,parameter]) := by
 unfold leftCode rightCode parameter
 rw [OriginalRootObservationNativeProof.nativeCalibration Q 1 arity [] contextCode leftTerm,
     OriginalRootObservationNativeProof.nativeCalibration Q 1 arity [] contextCode rightTerm]
 let a := OriginalRootObservation.typedValue Q contextCode (⟨.ground,bottom⟩ : Packed (Fin 1) arity [])
 let b := OriginalRootObservation.typedValue Q contextCode (⟨.ground,zero⟩ : Packed (Fin 1) arity [])
 have hp : ([a,b] : List Nat).Perm [b,a] := List.Perm.swap _ _ _
 have hs := OriginalHereditaryObservationRootUniformityProof.sortedPerm hp
 change Nat.pair 4 (Nat.pair 0 (Nat.pair 2
   (NumberedMultisetNumeric.numbersNumber ([a,b].insertionSort (· ≤ ·))))) =
   Nat.pair 4 (Nat.pair 0 (Nat.pair 2
   (NumberedMultisetNumeric.numbersNumber ([b,a].insertionSort (· ≤ ·)))))
 rw [hs]
theorem emptyRows (Q : Program 2) (input : Nat) :
 evaluate (OriginalHereditaryDeletionRows.rows Q) (List.Vector.ofFn ![input,parameter]) = 0 := by
 rw [OriginalHereditaryDeletionRowsBoundProof.nativeRows]
 have hl := OriginalContextInsertionCalibrationProof.lengthContext ([] : List Ty)
 simp only [parameter,Nat.unpair_pair,typesNumber]
 change NumberedMultisetNumeric.numbersNumber
   (OriginalHereditaryDeletionRows.values Q (evaluate OriginalContextInsertion.length
     (List.Vector.ofFn ![Encodable.encode ([] : List Ty)])) input parameter) = 0
 rw [hl]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelObservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelObservationProof
