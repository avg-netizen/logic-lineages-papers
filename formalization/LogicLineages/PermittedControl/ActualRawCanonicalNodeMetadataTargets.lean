module
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTargets
public import LogicLineages.PermittedControl.ActualRawComparisonCeilingTargets
public import LogicLineages.PermittedControl.ActualBoundedSignedRoutesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadata
open PreparedProjection (LowerOperandCode)
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (RawTerm encodeTerm groupRaw groupTyped)
open ActualRawComparisonCeiling (LabelCode encodeLabel labelCode)
open ActualFullValueLabels (activeLabel labels)
open ActualFullLabelPairGuards (Answer)
open ActualFullValueMaximalMetadata (flags classFlags)
open ActualBoundedSignedRoutes (activeTest)

def activeLabelCode (t : RawTerm) : Option LabelCode :=
  if t.1 = 0 then none else labelCode t.2

def labelsCode (ts : List RawTerm) : List LabelCode := ts.filterMap activeLabelCode

def nonlinearCode (op : LowerOperandCode) : Bool :=
  if op.1 = 1 then
    if op.2.2.1 = 0 then decide (0 < op.2.2.2.1) else true
  else decide (op.1 = 2)

def highestCode (top : Nat) (t : RawTerm) : Bool :=
  decide (t.1 ≠ 0 ∧ t.2.2.1 = top) && nonlinearCode t.2

def tapeHighestCode (top : Nat) (ts : List RawTerm) : Bool := ts.any (highestCode top)

def notLessCode (a : Nat) : Bool := decide (a ≠ 0)

def flagsCode (w n : Nat) (as : List Nat) : List Bool :=
  (List.range n).map (fun j => ((as.drop (j*w)).take w).all notLessCode)

def classFlagsCode (ts : List RawTerm) (as : List Nat) : List Bool :=
  let w := (labelsCode ts).length
  flagsCode w w as

def ExactRawActiveLabelTape : Prop :=
  (∀ t : WeightedOperand, activeLabelCode (encodeTerm t) = (activeLabel t).map encodeLabel) ∧
  ∀ ts : List WeightedOperand, labelsCode (ts.map encodeTerm) = (labels ts).map encodeLabel

def ExactRawHighestActivity : Prop :=
  (∀ (top : Nat) (t : WeightedOperand), highestCode top (encodeTerm t) = activeTest top t) ∧
  ∀ (top : Nat) (ts : List WeightedOperand),
    tapeHighestCode top (ts.map encodeTerm) = ts.any (activeTest top)

def ExactRawSuppliedAnswerFlags : Prop :=
  (∀ (w n : Nat) (as : List Answer),
      flagsCode w n (as.map Answer.code) = flags w n as) ∧
  ∀ (ts : List WeightedOperand) (as : List Answer),
    classFlagsCode (ts.map encodeTerm) (as.map Answer.code) = classFlags (labels ts) as

def ExactRawCanonicalNodeCalibration : Prop :=
  ∀ (top : Nat) (ts : List WeightedOperand) (as : List Answer),
    let raw := groupRaw (ts.map encodeTerm)
    let grouped := groupTyped ts
    labelsCode raw = (labels grouped).map encodeLabel ∧
    tapeHighestCode top raw = grouped.any (activeTest top) ∧
    classFlagsCode raw (as.map Answer.code) = classFlags (labels grouped) as

def ExactRawCanonicalNodeEffectivity : Prop :=
  Primrec activeLabelCode ∧ Primrec labelsCode ∧ Primrec₂ highestCode ∧
  Primrec₂ tapeHighestCode ∧
  Primrec (fun p : Nat × Nat × List Nat => flagsCode p.1 p.2.1 p.2.2) ∧
  Primrec₂ classFlagsCode

def FullActualRawCanonicalNodeMetadata : Prop :=
  ExactRawActiveLabelTape ∧ ExactRawHighestActivity ∧ ExactRawSuppliedAnswerFlags ∧
    ExactRawCanonicalNodeCalibration ∧ ExactRawCanonicalNodeEffectivity

end LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadata
