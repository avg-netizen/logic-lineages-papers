module
public import LogicLineages.PermittedControl.ActualCountCoreLabelsTargets
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.OrdinalComparison.RawComparisonProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountCoreLabels
open OrdinalComparison FieldComparison
open SelectedCountOnlyClass (omegaSquareNote prefixTarget)

private theorem shapeGuard (lam mu : NONote) :
    closedProperEntryGuard (rawNoteEncode lam.1,rawNoteEncode mu.1,rawNormCode (rawNoteEncode lam.1)) = true ↔
      ProperField (.entry 0 lam mu) := by
  have h := closedProperEntryDomainExact.2.2 lam mu (rawNormCode (rawNoteEncode lam.1))
  change _ ↔ ProperField (.entry 0 lam mu) ∧
    actualOrdinalNorm lam.1.repr ≤ rawNormCode (rawNoteEncode lam.1) at h
  simpa only [normal_norm_code lam,le_refl,and_true] using h

private theorem prefixCode (mu : NONote) :
    ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode omegaSquareNote.1) =
      rawNoteEncode (prefixTarget mu).1 := ordinal_add_note_code mu omegaSquareNote

private theorem labelCode (lam mu : NONote) :
    rawLabel (rawNoteEncode lam.1) (rawNoteEncode mu.1) = (fieldLabel lam mu).map longFieldCode := by
  cases code : rawTag (rawNoteEncode lam.1) (rawNoteEncode mu.1) with
  | zero => simp [rawLabel,fieldLabel,classify,code]
  | succ t =>
      cases t with
      | zero => simp [rawLabel,fieldLabel,classify,code]
      | succ t =>
          cases t with
          | zero => simp [rawLabel,fieldLabel,classify,code,longFieldCode]
          | succ t =>
              cases t with
              | zero => simp [rawLabel,fieldLabel,classify,code,longFieldCode,prefixCode]
              | succ t => simp [rawLabel,fieldLabel,classify,code]

theorem exactCountCoreClassifier : ExactCountCoreClassifier := by
  intro lam mu
  let l := rawNoteEncode lam.1
  let m := rawNoteEncode mu.1
  let eta := prefixTarget mu
  let k := shortGapLength lam mu
  let guarded := closedProperEntryGuard (l,m,rawNormCode l)
  have rawShape : guarded = true ↔ ProperField (.entry 0 lam mu) := shapeGuard lam mu
  have compar := rawComparisonOrdinalCorrect eta lam
  have emitLong (tag : Nat) (shape : ProperField (.entry 0 lam mu)) (zero : k = 0)
      (classCode :
        (if rawComparisonCode (rawNoteEncode eta.1) l = 1 then 2
        else if rawComparisonCode (rawNoteEncode eta.1) l = 0 then 3 else 0) = tag) :
      rawTag l m = tag := by
    have guard : closedProperEntryGuard (l,m,rawNormCode l) = true := rawShape.mpr shape
    have isZero : shortGapLengthCode l m = 0 := zero
    unfold rawTag
    rw [if_pos guard,if_pos isZero]
    change (if rawComparisonCode (ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode omegaSquareNote.1))
        (rawNoteEncode lam.1) = 1 then 2
      else if rawComparisonCode (ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode omegaSquareNote.1))
        (rawNoteEncode lam.1) = 0 then 3 else 0) = tag
    rw [prefixCode]
    exact classCode
  refine ⟨?_,?_,?_,?_,?_,labelCode lam mu⟩
  · intro invalid
    have guard : ¬ closedProperEntryGuard (l,m,rawNormCode l) = true :=
      fun h => invalid (rawShape.mp h)
    have tag : rawTag l m = 0 := by simp only [rawTag,if_neg guard]
    simp only [classify,show rawTag (rawNoteEncode lam.1) (rawNoteEncode mu.1) = 0 from tag]
  · intro shape positive
    have guard : closedProperEntryGuard (l,m,rawNormCode l) = true := rawShape.mpr shape
    have nonzero : ¬ shortGapLengthCode l m = 0 := Nat.ne_of_gt positive
    have tag : rawTag l m = 1 := by simp only [rawTag,guard,if_true,if_neg nonzero]
    simp only [classify,show rawTag (rawNoteEncode lam.1) (rawNoteEncode mu.1) = 1 from tag]
  · intro shape zero equal
    have eq : rawComparisonCode (rawNoteEncode eta.1) l = 1 := compar.2.1.mpr equal
    have tag := emitLong 2 shape zero (by rw [if_pos eq])
    simp only [classify,show rawTag (rawNoteEncode lam.1) (rawNoteEncode mu.1) = 2 from tag]
  · intro shape zero proper
    have lt : rawComparisonCode (rawNoteEncode eta.1) l = 0 := compar.1.mpr proper
    have noEq : ¬ rawComparisonCode (rawNoteEncode eta.1) l = 1 := by rw [lt]; decide
    have tag := emitLong 3 shape zero (by rw [if_neg noEq,if_pos lt])
    simp only [classify,show rawTag (rawNoteEncode lam.1) (rawNoteEncode mu.1) = 3 from tag]
  · intro shape zero bad
    have gt : rawComparisonCode (rawNoteEncode eta.1) l = 2 := compar.2.2.mpr bad
    have noEq : ¬ rawComparisonCode (rawNoteEncode eta.1) l = 1 := by rw [gt]; decide
    have noLess : ¬ rawComparisonCode (rawNoteEncode eta.1) l = 0 := by rw [gt]; decide
    have tag := emitLong 0 shape zero (by rw [if_neg noEq,if_neg noLess])
    simp only [classify,show rawTag (rawNoteEncode lam.1) (rawNoteEncode mu.1) = 0 from tag]

end LogicLineages.PermittedControl.ActualCountCoreLabels
