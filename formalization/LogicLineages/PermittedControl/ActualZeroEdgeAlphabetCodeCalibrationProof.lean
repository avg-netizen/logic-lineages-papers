module
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodeTargets
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCode
open OrdinalComparison PreparedProjection FieldComparison
open ActualZeroClassCommonTail ActualZeroEdgeAlphabet ConcreteCountPairReplacement
open SelectedCountOnlyClass (omegaSquareNote prefixTarget)

private theorem prefixChoiceLiteral (op : LowerOperand) :
    prefixChoiceCode op.code = (prefixLabel (1,op)).map encodePrefix := by
  cases op with
  | coordinate rank => rfl
  | ordinary rank field => rfl
  | count rank lam mu =>
      change some (rank,rawNoteEncode lam.1,
          ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode omegaSquareNote.1)) =
        some (rank,rawNoteEncode lam.1,rawNoteEncode (prefixTarget mu).1)
      rw [ordinal_add_note_code mu omegaSquareNote] <;> rfl

private theorem prefixChoicesLiteral (alphabet : List LowerOperand) :
    prefixChoicesCode (alphabet.map LowerOperand.code) =
      (prefixCandidates alphabet).map encodePrefix := by
  induction alphabet with
  | nil => rfl
  | cons op tail ih =>
      cases h : prefixLabel (1,op) with
      | none =>
          simp only [prefixChoicesCode,prefixCandidates,List.map_cons,List.filterMap_cons,
            prefixChoiceLiteral,h,Option.map_none]
          exact ih
      | some p =>
          simp only [prefixChoicesCode,prefixCandidates,List.map_cons,List.filterMap_cons,
            prefixChoiceLiteral,h,Option.map_some]
          exact congrArg (List.cons (encodePrefix p)) ih

private theorem prefixKeyLiteral (label : PrefixLabel) :
    prefixKeyCode (encodePrefix label) = (prefixOperand label).code := rfl

private theorem pairKeyLiteral (lo hi : PrefixLabel) :
    pairKeyCode (encodePrefix lo) (encodePrefix hi) = (pairOperand lo hi).code := by
  simp only [pairKeyCode,encodePrefix,replacementCode,pairOperand,replacementOperand,
    LowerOperand.code,longFieldCode]
  rw [ordinal_sub_note_code,ordinal_add_note_code]

private theorem pairChoiceLiteral (lo hi : PrefixLabel) :
    pairChoiceCode (encodePrefix lo) (encodePrefix hi) =
      if lo.rank < hi.rank then some ((pairOperand lo hi).code) else none := by
  change (if lo.rank < hi.rank then some (pairKeyCode (encodePrefix lo) (encodePrefix hi)) else none) = _
  rw [pairKeyLiteral]

private theorem choicesForLiteral (lo : PrefixLabel) (labels : List PrefixLabel) :
    (labels.map encodePrefix).filterMap (pairChoiceCode (encodePrefix lo)) =
      ((labels.filter (fun hi => decide (lo.rank < hi.rank))).map (pairOperand lo)).map LowerOperand.code := by
  induction labels with
  | nil => rfl
  | cons hi labels ih =>
      by_cases order : lo.rank < hi.rank
      · have shape : (hi::labels).filter (fun p => decide (lo.rank < p.rank)) =
            hi :: labels.filter (fun p => decide (lo.rank < p.rank)) := by simp [order]
        simp only [List.map_cons,List.filterMap_cons,pairChoiceLiteral,if_pos order,shape]
        exact congrArg (List.cons ((pairOperand lo hi).code)) ih
      · have shape : (hi::labels).filter (fun p => decide (lo.rank < p.rank)) =
            labels.filter (fun p => decide (lo.rank < p.rank)) := by simp [order]
        simp only [List.map_cons,List.filterMap_cons,pairChoiceLiteral,if_neg order,shape]
        exact ih

private theorem pairsForLiteral (lowers labels : List PrefixLabel) :
    (lowers.map encodePrefix).flatMap
        (fun lo => (labels.map encodePrefix).filterMap (pairChoiceCode lo)) =
      (lowers.flatMap (fun lo =>
        (labels.filter (fun hi => decide (lo.rank < hi.rank))).map (pairOperand lo))).map LowerOperand.code := by
  induction lowers with
  | nil => rfl
  | cons lo lowers ih =>
      simp only [List.map_cons,List.flatMap_cons,List.map_append,choicesForLiteral,ih]

private theorem expandLiteral (alphabet : List LowerOperand) :
    expandCode (alphabet.map LowerOperand.code) = (expand alphabet).map LowerOperand.code := by
  simp only [expandCode,expand,prefixChoicesLiteral,pairChoicesCode,pairCandidates,
    pairsForLiteral,List.map_append,List.map_map,Function.comp_def,prefixKeyLiteral]

private theorem expandCommutes (n : Nat) (alphabet : List LowerOperand) :
    expandSteps n (expand alphabet) = expand (expandSteps n alphabet) := by
  induction n generalizing alphabet with
  | zero => rfl
  | succ n ih => exact ih (expand alphabet)

private theorem stepsLiteral (n : Nat) (alphabet : List LowerOperand) :
    expandStepsCode n (alphabet.map LowerOperand.code) = (expandSteps n alphabet).map LowerOperand.code := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change expandCode (expandStepsCode n (alphabet.map LowerOperand.code)) =
        (expandSteps n (expand alphabet)).map LowerOperand.code
      rw [ih,expandLiteral,expandCommutes n alphabet]

private theorem collectLiteral (budget : Nat) (alphabet : List LowerOperand) :
    collectCode budget (alphabet.map LowerOperand.code) =
      ((List.range (budget+1)).flatMap (fun depth => expandSteps depth alphabet)).map LowerOperand.code := by
  unfold collectCode
  generalize List.range (budget+1) = depths
  induction depths with
  | nil => rfl
  | cons depth depths ih => simp only [List.flatMap_cons,List.map_append,stepsLiteral,ih]

theorem codeCalibration : CodeCalibration := ⟨expandLiteral,stepsLiteral,collectLiteral⟩

end LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCode
