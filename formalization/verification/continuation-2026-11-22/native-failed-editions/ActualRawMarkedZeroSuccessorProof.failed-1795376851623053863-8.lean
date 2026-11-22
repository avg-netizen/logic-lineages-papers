module
public import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorTargets
import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorPlanProof
import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorMoveProof
import LogicLineages.PermittedControl.ActualRawSignedCleanupProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
open MixedSameRankResidue ActualSymbolicZeroSuccessor ActualZeroSuccessorMarkedClass
open ActualZeroSuccessorPrefixPlan ActualRawSignedCleanup ActualRawSignedStaticCeiling

private theorem shiftsCalibration (ms : List Marked) :
    shiftsCode (ms.map encodeMark) = originShifts ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    change shiftAddCode (shiftOneCode (encodeMark m)) (shiftsCode (ms.map encodeMark)) =
      originShifts (m::ms)
    rw [oneShiftCalibration,ih]
    rfl

private theorem cohortCalibration (ms : List Marked) :
    cohortCode (ms.map encodeMark) = (cohortSyntax ms).map encodePrefix := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    change ((encodeMark m :: ms.map encodeMark).filterMap markedPrefixCode) =
      ((m::ms).filterMap markedPrefix).map encodePrefix
    simp only [List.filterMap_cons,onePrefixCalibration]
    cases shape : markedPrefix m with
    | none => exact ih
    | some p => exact congrArg (List.cons (encodePrefix p)) ih

private theorem outsideCalibration (ms : List Marked) :
    outsideCode (ms.map encodeMark) = (outsideSyntax ms).map encodeWeighted := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [outsideCode,outsideSyntax,List.map_cons,List.filter_cons,List.filter_cons]
    have same : (decide ((encodeMark m).1.1 ≠ 0) && !(encodeMark m).2) = kept m := rfl
    rw [same]
    cases h : kept m with
    | false => exact ih
    | true => exact congrArg (List.cons (encodeWeighted m.1)) ih

theorem exactRawMarkedSuccessor : ExactRawMarkedSuccessor := by
  intro constant ms
  let ps := cohortSyntax ms
  let before := outsideSyntax ms ++ movedSyntax (leastSyntax ps) ps
  have arranged : outsideCode (ms.map encodeMark) ++
      movedCode (leastCode (cohortCode (ms.map encodeMark))) (cohortCode (ms.map encodeMark)) =
      before.map encodeWeighted := by
    rw [outsideCalibration,cohortCalibration,leastCalibration,moveCalibration]
    exact (List.map_append _ _).symm
  unfold markedSuccessorCode successorFromMarks
  simp only [Prod.mk_snd,Prod.mk_fst,shiftsCalibration]
  cases status : originShifts ms with
  | none => rfl
  | some delta =>
    change some (cleanupCode (constant+delta,
      outsideCode (ms.map encodeMark) ++
        movedCode (leastCode (cohortCode (ms.map encodeMark))) (cohortCode (ms.map encodeMark)))) =
      some (encodeSyntax ⟨constant+delta+cleanupShift before,cleanSyntax before⟩)
    rw [arranged]
    change some (constant+delta+shiftCode (before.map encodeWeighted),retainCode (before.map encodeWeighted)) = _
    rw [shiftCalibration,retainCalibration]
    rfl

end LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
