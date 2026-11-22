module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowCoverBoundsAlgorithm (bounds termMeasure table)
open NumberedWindowFieldAlgorithm (unpackNode pack)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run field cursor nodeGood)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowRawExchangeVerticesBoundsTableProof (termBounds previous)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverNamedLeafMeasureNumericProof (exact_CoverNamedLeafSharedMeasure)
open NumberedWindowInternalCoverLambdaMeasureRowNumericProof (exact_CoverLambdaBumpCalibration)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaBump)
open NumberedWindowInternalCoverOrdinaryMeasureTargets
open NumberedWindowInternalCoverOrdinaryMeasureNumericProof (exact_CoverSelectedArgsMeasure exact_CoverOrdinarySharedMeasure)
open NumberedWindowInternalCoverNumberedMeasureCombineTargets (numberedJoin)
open NumberedWindowInternalCoverNumberedMeasureCombineNumericProof (exact_CoverNumberedJoin)
open InternalEqualityTestEvaluationProof (vectorThree)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets

private theorem numeralAndArgs {raw h ty k l r : Nat}
    (read : unpackNode raw = some (5,[h,ty,k,l,r])) :
    run (field 2) raw = k ∧ run (field 3) raw = l ∧ run (field 4) raw = r := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 5 (pack [h,ty,k,l,r]))).2
  have before : run cellTail (pack [h,ty,k,l,r]) = pack [ty,k,l,r] :=
    (headTailOfCell (cellAt h (pack [ty,k,l,r]))).2
  have second : run cellTail (pack [ty,k,l,r]) = pack [k,l,r] :=
    (headTailOfCell (cellAt ty (pack [k,l,r]))).2
  have id : run cellHead (pack [k,l,r]) = k := (headTailOfCell (cellAt k (pack [l,r]))).1
  have third : run cellTail (pack [k,l,r]) = pack [l,r] :=
    (headTailOfCell (cellAt k (pack [l,r]))).2
  have left : run cellHead (pack [l,r]) = l := (headTailOfCell (cellAt l (pack [r]))).1
  have fourth : run cellTail (pack [l,r]) = pack [r] := (headTailOfCell (cellAt l (pack [r]))).2
  have right : run cellHead (pack [r]) = r := (headTailOfCell (cellAt r (pack []))).1
  change run (field 2) (NumberedWindowPairAlgorithm.pair 5 (pack [h,ty,k,l,r]) + 1) = k ∧
    run (field 3) (NumberedWindowPairAlgorithm.pair 5 (pack [h,ty,k,l,r]) + 1) = l ∧
    run (field 4) (NumberedWindowPairAlgorithm.pair 5 (pack [h,ty,k,l,r]) + 1) = r
  simp only [field,cursor,applyValue,outer,before,second,id,third,left,fourth,right] <;> simp

private theorem actualBounds {raw h ty k l r : Nat} (read : unpackNode raw = some (5,[h,ty,k,l,r])) :
    (bounds raw).1 = ((bounds l).2.1+(bounds r).2.1+1,max k (max (bounds l).2.2 (bounds r).2.2)) := by
  have beforeL := (nodeBounds read).2 l (by simp)
  have beforeR := (nodeBounds read).2 r (by simp)
  rw [termBounds read]
  change (((table raw).getD l default).2.1+((table raw).getD r default).2.1+1,
    max k (max ((table raw).getD l default).2.2 ((table raw).getD r default).2.2)) = _
  rw [previous beforeL,previous beforeR]

private theorem opValue (A : Program 1) (raw : Nat) :
    evaluate (numberedMeasureApply A) (raw ::ᵥ nil) = evaluate numberedJoin
      (run (field 2) raw ::ᵥ evaluate (selectedArgsMeasure A) (run (field 3) raw ::ᵥ nil) ::ᵥ
        evaluate (selectedArgsMeasure A) (run (field 4) raw ::ᵥ nil) ::ᵥ nil) := by
  change evaluate numberedJoin (List.Vector.ofFn (fun i =>
    evaluate ((![field 2,numberedArgCode A 3,numberedArgCode A 4] : Fin 3 → Program 1) i)
      (raw ::ᵥ nil))) = _
  rw [vectorThree] <;> rfl

theorem exact_CoverNumberedMeasureBase : ExactCoverNumberedMeasureBase := by
  intro M A calibrated args raw
  change evaluate (numberedMeasureBase M A) (raw ::ᵥ nil) = Encodable.encode (bounds raw).1
  rw [numberedMeasureBase,evalBranch]
  by_cases yes : run (header 5 5) raw = 1
  · obtain ⟨fs,read,len⟩ := (exact_CoverHeaderUnpackNode 5 5 raw).mp yes
    rcases fs with _ | ⟨h,_ | ⟨ty,_ | ⟨k,_ | ⟨l,_ | ⟨r,_ | ⟨extra,rest⟩⟩⟩⟩⟩⟩ <;> simp at len
    change evaluate (header 5 5) (raw ::ᵥ nil) = 1 at yes
    rw [yes,if_neg (by decide),opValue]
    obtain ⟨q,ls,rs⟩ := numeralAndArgs read
    rw [q,ls,rs,exact_CoverSelectedArgsMeasure A args l,exact_CoverSelectedArgsMeasure A args r,actualBounds read]
    exact exact_CoverNumberedJoin k (bounds l).2.1 (bounds r).2.1 (bounds l).2.2 (bounds r).2.2
  · have zero : run (header 5 5) raw = 0 := by
      have bits : run (header 5 5) raw = 0 ∨ run (header 5 5) raw = 1 := by
        unfold run header nodeGood
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bits.resolve_right yes
    change evaluate (header 5 5) (raw ::ᵥ nil) = 0 at zero
    rw [if_pos zero]
    exact calibrated raw

theorem exact_CoverNumberedSharedMeasure : ExactCoverNumberedSharedMeasure := by
  intro M A original arg
  exact exact_CoverOrdinarySharedMeasure (numberedMeasureBase M A) A
    (exact_CoverNumberedMeasureBase M A original arg) arg

#print axioms exact_CoverNumberedMeasureBase
#print axioms exact_CoverNumberedSharedMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedNumericProof
