module
public import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorTargets
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
open OrdinalComparison FieldComparison PreparedProjection
open ActualCountCoreLabels (rawTag classify)
open ActualSymbolicZeroSuccessor ActualZeroSuccessorPrefixPlan ActualZeroSuccessorMarkedClass
open SelectedCountOnlyClass (omegaSquareNote prefixTarget)

private theorem etaCalibration (mu : NONote) :
    etaCode (rawNoteEncode mu.1) = rawNoteEncode (prefixTarget mu).1 :=
  ordinal_add_note_code mu omegaSquareNote

private theorem coreCalibration (mu : NONote) :
    coreCode (rawNoteEncode mu.1) = Targets.countCoreConstant mu.1.repr := by
  simp only [coreCode,Targets.countCoreConstant,normal_norm_code]

theorem planCalibration (lam mu : NONote) :
    planCode (rawNoteEncode lam.1,rawNoteEncode mu.1) = encodePlan (countPlan lam mu) := by
  unfold planCode countPlan classify
  generalize rawTag (rawNoteEncode lam.1) (rawNoteEncode mu.1) = tag
  cases tag with
  | zero => rfl
  | succ tag =>
    cases tag with
    | zero => rfl
    | succ tag =>
      cases tag with
      | zero => rfl
      | succ tag =>
        cases tag with
        | zero =>
          change some (1,etaCode (rawNoteEncode mu.1),
            shortGapLengthCode (rawNoteEncode lam.1) (etaCode (rawNoteEncode mu.1))) = _
          rw [etaCalibration]
          change some (1,rawNoteEncode (prefixTarget mu).1,shortGapLength lam (prefixTarget mu)) = _
          by_cases zero : shortGapLength lam (prefixTarget mu) = 0
          · simp only [if_pos zero,encodePlan,zero]
          · simp only [if_neg zero,encodePlan]
        | succ tag => rfl

theorem oneShiftCalibration (m : Marked) : shiftOneCode (encodeMark m) = originShift m := by
  rcases m with ⟨⟨w,op⟩,selected⟩
  cases selected with
  | false => rfl
  | true =>
    cases op with
    | coordinate n => rfl
    | ordinary n F => rfl
    | count n lam mu =>
      change (planCode (rawNoteEncode lam.1,rawNoteEncode mu.1)).map
        (fun plan => w * (coreCode (rawNoteEncode mu.1) + (plan.2.2 : Int))) =
          (match countPlan lam mu with
          | .identity | .survives _ => some (w * Targets.countCoreConstant mu.1.repr)
          | .short _ k => some (w * (Targets.countCoreConstant mu.1.repr + (k : Int)))
          | .invalid => none)
      rw [planCalibration,coreCalibration]
      cases countPlan lam mu <;> simp [encodePlan]

theorem onePrefixCalibration (m : Marked) :
    markedPrefixCode (encodeMark m) = (markedPrefix m).map encodePrefix := by
  rcases m with ⟨⟨w,op⟩,selected⟩
  cases selected with
  | false => rfl
  | true =>
    cases op with
    | coordinate n => rfl
    | ordinary n F => rfl
    | count n lam mu =>
      change (planCode (rawNoteEncode lam.1,rawNoteEncode mu.1)).bind
        (fun plan => if plan.1 = 1 ∧ plan.2.2 = 0 then
            some (n,rawNoteEncode lam.1,plan.2.1,w) else none) =
          (match countPlan lam mu with
          | .survives eta => some ({ rank := n, lam := lam, eta := eta, weight := w } : PrefixSyntax)
          | _ => none).map encodePrefix
      rw [planCalibration]
      cases verdict : countPlan lam mu with
      | invalid => rfl
      | identity => rfl
      | survives eta => rfl
      | short eta k =>
        have nz : k ≠ 0 := by
          cases shape : classify lam mu with
          | invalid => simp [countPlan,shape] at verdict
          | shortCount j => simp [countPlan,shape] at verdict
          | identityPrefix => simp [countPlan,shape] at verdict
          | properPrefix endpoint =>
            by_cases absent : shortGapLength lam endpoint = 0
            · simp [countPlan,shape,absent] at verdict
            · rw [countPlan,shape,if_neg absent] at verdict
              cases verdict
              exact absent
        simp [encodePlan,nz]

theorem exactRawMarkedPlan : ExactRawMarkedPlan :=
  ⟨planCalibration,fun m => ⟨oneShiftCalibration m,onePrefixCalibration m⟩⟩

end LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
