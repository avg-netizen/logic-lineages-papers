module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalTypedArgumentObservations NumberedMultisetNumeric
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof InternalListCodecEvaluationProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

theorem remainingEvaluation (raw acc : Nat) :
 evaluate reverseRemaining (Nat.pair raw acc ::ᵥ nil) = raw := by
 rw [reverseRemaining,leftEvaluation]
 change (Nat.unpair (Nat.pair raw acc)).1 = raw
 rw [Nat.unpair_pair]

theorem accumulatedEvaluation (raw acc : Nat) :
 evaluate reverseAccumulated (Nat.pair raw acc ::ᵥ nil) = acc := by
 rw [reverseAccumulated,rightEvaluation]
 change (Nat.unpair (Nat.pair raw acc)).2 = acc
 rw [Nat.unpair_pair]

theorem advanceEvaluation (head tail acc : Nat) :
 evaluate reverseAdvance (Nat.pair (1+Nat.pair head tail) acc ::ᵥ nil) =
 Nat.pair tail (1+Nat.pair head acc) := by
 rw [reverseAdvance,pairOfEvaluation,consOfEvaluation]
 have ht : evaluate (.composition InternalListCodec.tailCode (fun _ : Fin 1 => reverseRemaining))
     (Nat.pair (1+Nat.pair head tail) acc ::ᵥ nil) = tail := by
   change evaluate InternalListCodec.tailCode (ofFn fun _ : Fin 1 => evaluate reverseRemaining _) = _
   rw [vectorOne,remainingEvaluation,tailEvaluation]
   simp [Nat.add_comm 1,Nat.unpair_pair]
 have hh : evaluate (.composition InternalListCodec.headCode (fun _ : Fin 1 => reverseRemaining))
     (Nat.pair (1+Nat.pair head tail) acc ::ᵥ nil) = head := by
   change evaluate InternalListCodec.headCode (ofFn fun _ : Fin 1 => evaluate reverseRemaining _) = _
   rw [vectorOne,remainingEvaluation,headEvaluation]
   simp [Nat.add_comm 1,Nat.unpair_pair]
 rw [ht,hh,accumulatedEvaluation]

theorem stepNil (acc : Nat) : evaluate reverseStep (Nat.pair 0 acc ::ᵥ nil) = Nat.pair 0 acc := by
 rw [reverseStep,evalBranch,remainingEvaluation]
 rfl

theorem stepCons (head tail acc : Nat) :
 evaluate reverseStep (Nat.pair (1+Nat.pair head tail) acc ::ᵥ nil) = Nat.pair tail (1+Nat.pair head acc) := by
 rw [reverseStep,evalBranch,remainingEvaluation]
 simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,false_and,ite_false]
 exact advanceEvaluation head tail acc

theorem runZero (state : Nat) : evaluate reverseRun (0 ::ᵥ state ::ᵥ nil) = state := rfl

theorem runNext (fuel state : Nat) :
 evaluate reverseRun (fuel.succ ::ᵥ state ::ᵥ nil) =
 evaluate reverseStep (evaluate reverseRun (fuel ::ᵥ state ::ᵥ nil) ::ᵥ nil) := by
 change evaluate reverseStep (ofFn fun _ : Fin 1 => evaluate reverseRun (fuel ::ᵥ state ::ᵥ nil)) = _
 rw [vectorOne]

theorem runFirst (fuel state : Nat) :
 evaluate reverseRun (fuel.succ ::ᵥ state ::ᵥ nil) =
 evaluate reverseRun (fuel ::ᵥ evaluate reverseStep (state ::ᵥ nil) ::ᵥ nil) := by
 induction fuel with
 | zero => rw [runNext,runZero,runZero]
 | succ fuel ih => rw [runNext,ih,runNext]

theorem runList (xs acc : List Nat) (fuel : Nat) (hf : xs.length ≤ fuel) :
 evaluate reverseRun (fuel ::ᵥ Nat.pair (numbersNumber xs) (numbersNumber acc) ::ᵥ nil) =
 Nat.pair 0 (numbersNumber (xs.reverse ++ acc)) := by
 induction xs generalizing acc fuel with
 | nil =>
   simp only [List.reverse_nil,List.nil_append,numbersNumber]
   induction fuel with
   | zero => rfl
   | succ fuel ih => rw [runNext,ih (Nat.zero_le _) ,stepNil]
 | cons head tail ih =>
   cases fuel with
   | zero => simp at hf
   | succ fuel =>
     rw [runFirst]
     simp only [numbersNumber,stepCons]
     simpa only [numbersNumber,List.reverse_cons,List.append_assoc,List.singleton_append] using
       ih (head::acc) fuel (Nat.le_of_succ_le_succ hf)

theorem nativeReverse : OriginalTypedArgumentObservationsTargets.NativeReverse := by
 intro xs
 change evaluate (rightOf (.composition reverseRun
   ![OriginalRawSyntaxTransport.succOf (.projection 0),pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)]))
   (numbersNumber xs ::ᵥ nil) = _
 rw [rightOfEvaluation]
 have h : evaluate (.composition reverseRun
   ![OriginalRawSyntaxTransport.succOf (.projection 0),pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)])
   (numbersNumber xs ::ᵥ nil) = Nat.pair 0 (numbersNumber xs.reverse) := by
   change evaluate reverseRun (ofFn fun k : Fin 2 => evaluate
     ((![OriginalRawSyntaxTransport.succOf (.projection 0),pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)] : Fin 2 → Program 1) k)
     (numbersNumber xs ::ᵥ nil)) = _
   rw [vectorTwo]
   change evaluate reverseRun (evaluate (OriginalRawSyntaxTransport.succOf (.projection 0)) (numbersNumber xs ::ᵥ nil) ::ᵥ
     evaluate (pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)) (numbersNumber xs ::ᵥ nil) ::ᵥ nil) = _
   rw [pairOfEvaluation]
   change evaluate reverseRun ((numbersNumber xs).succ ::ᵥ Nat.pair (numbersNumber xs) 0 ::ᵥ nil) = _
   simpa only [numbersNumber,List.append_nil] using runList xs [] (numbersNumber xs).succ
     (Nat.le_trans (NumberedMultisetNumericTotalityProof.encodedLengthBound xs) (Nat.le_succ _))
 rw [h,Nat.unpair_pair]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseProof
