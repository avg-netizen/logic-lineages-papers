module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataTargets
import LogicLineages.PermittedControl.ActualRawComparisonCeilingProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadata
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (WeightedOperand)
open ActualRawComparisonCeiling (encodeLabel labelCalibration)
open ActualCanonicalOperandGrouping (encodeTerm exactCanonicalTape)
open ActualFullValueLabels (activeLabel labels)
open ActualFullLabelPairGuards (Answer)
open ActualFullValueMaximalMetadata (flags classFlags notLess)
open ActualBoundedSignedRoutes (activeTest nonlinear)

theorem labelCalibrationOne (t : WeightedOperand) :
    activeLabelCode (encodeTerm t) = (activeLabel t).map encodeLabel := by
  unfold activeLabelCode activeLabel encodeTerm
  rw [labelCalibration]
  split <;> rfl

theorem labelsCalibration (ts : List WeightedOperand) :
    labelsCode (ts.map encodeTerm) = (labels ts).map encodeLabel := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change (encodeTerm t :: ts.map encodeTerm).filterMap activeLabelCode =
      ((t :: ts).filterMap activeLabel).map encodeLabel
    simp only [List.filterMap_cons,labelCalibrationOne]
    cases h : activeLabel t with
    | none =>
      simp only [h,Option.map_none]
      exact ih
    | some l =>
      simp only [h,Option.map_some]
      exact congrArg (List.cons (encodeLabel l)) ih

theorem exactRawActiveLabelTape : ExactRawActiveLabelTape := ⟨labelCalibrationOne,labelsCalibration⟩

private theorem nonlinearLiteral (op : LowerOperand) : nonlinearCode op.code = nonlinear op := by
  cases op with
  | coordinate k => rfl
  | count k lam mu => rfl
  | ordinary k field => cases field <;> rfl

private theorem rankLiteral (op : LowerOperand) : op.code.2.1 = op.rank := by
  cases op <;> rfl

theorem highestCalibration (top : Nat) (t : WeightedOperand) :
    highestCode top (encodeTerm t) = activeTest top t := by
  unfold highestCode activeTest encodeTerm
  rw [rankLiteral,nonlinearLiteral]

theorem tapeHighestCalibration (top : Nat) (ts : List WeightedOperand) :
    tapeHighestCode top (ts.map encodeTerm) = ts.any (activeTest top) := by
  simp only [tapeHighestCode,List.any_map,Function.comp_def,highestCalibration]

theorem exactRawHighestActivity : ExactRawHighestActivity := ⟨highestCalibration,tapeHighestCalibration⟩

private theorem allLiteral (as : List Answer) :
    (as.map Answer.code).all notLessCode = as.all notLess := by
  induction as with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons,List.all_cons,ih]
    cases a <;> rfl

private theorem flagsStep (w n : Nat) (as : List Nat) :
    flagsCode w (n+1) as = (as.take w).all notLessCode :: flagsCode w n (as.drop w) := by
  unfold flagsCode
  rw [List.range_succ_eq_map]
  simp only [List.map_cons,Nat.zero_mul,List.drop_zero,List.map_map,Function.comp_def]
  apply congrArg (List.cons ((as.take w).all notLessCode))
  apply congrArg (fun g : Nat → Bool => (List.range n).map g)
  funext j
  rw [List.drop_drop,Nat.succ_mul,Nat.add_comm w]

theorem flagsCalibration (w n : Nat) (as : List Answer) :
    flagsCode w n (as.map Answer.code) = flags w n as := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih =>
    rw [flagsStep,← List.map_take,← List.map_drop,allLiteral,ih] <;> rfl

theorem classFlagsCalibration (ts : List WeightedOperand) (as : List Answer) :
    classFlagsCode (ts.map encodeTerm) (as.map Answer.code) = classFlags (labels ts) as := by
  unfold classFlagsCode classFlags
  rw [labelsCalibration,List.length_map,flagsCalibration]

theorem exactRawSuppliedAnswerFlags : ExactRawSuppliedAnswerFlags :=
  ⟨flagsCalibration,classFlagsCalibration⟩

theorem exactRawCanonicalNodeCalibration : ExactRawCanonicalNodeCalibration := by
  intro top ts as
  simp only
  rw [← exactCanonicalTape.1 ts]
  exact ⟨labelsCalibration _,tapeHighestCalibration _ _,classFlagsCalibration _ _⟩

end LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadata
