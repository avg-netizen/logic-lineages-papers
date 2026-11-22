module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataTargets
public import LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClassTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeDecorator
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (RawTerm encodeTerm groupRaw groupTyped)
open ActualRawCanonicalNodeMetadata (activeLabelCode labelsCode classFlagsCode)
open ActualZeroSuccessorMarkedClass (Marked decorate)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Answer)
open ActualFullValueMaximalMetadata (classFlags)

abbrev RawMarked := RawTerm × Bool
abbrev State := List Bool × List RawMarked

def encodeMark (mark : Marked) : RawMarked := (encodeTerm mark.1,mark.2)

/-- The reversed output is private; the remaining mask is exact.
An active occurrence cannot read a default bit. -/
def paintStep (old : Option State) (term : RawTerm) : Option State :=
  old.bind fun p =>
    if (activeLabelCode term).isSome then
      p.1.head?.map (fun b => (p.1.tail,(term,b)::p.2))
    else some (p.1,(term,false)::p.2)

def paintFinish (old : Option State) : Option (List RawMarked) :=
  old.bind fun p => if p.1.length = 0 then some p.2.reverse else none

def decorateCode (ts : List RawTerm) (mask : List Bool) : Option (List RawMarked) :=
  paintFinish (ts.foldl paintStep (some (mask,[])))

def ExactRawDecorateCalibration : Prop :=
  ∀ (ts : List WeightedOperand) (mask : List Bool),
    decorateCode (ts.map encodeTerm) mask = (decorate ts mask).map (List.map encodeMark)

def ExactLiteralRawDecorationDomain : Prop :=
  ∀ (ts : List WeightedOperand) (mask : List Bool),
    ((decorateCode (ts.map encodeTerm) mask).isSome = true ↔ mask.length = (labelsCode (ts.map encodeTerm)).length) ∧
    ∀ ms : List RawMarked, decorateCode (ts.map encodeTerm) mask = some ms → ms.map Prod.fst = ts.map encodeTerm

def ExactCanonicalSuppliedDecoration : Prop :=
  ∀ (ts : List WeightedOperand) (answers : List Answer),
    let raw := groupRaw (ts.map encodeTerm)
    let grouped := groupTyped ts
    decorateCode raw (classFlagsCode raw (answers.map Answer.code)) =
      (decorate grouped (classFlags (labels grouped) answers)).map (List.map encodeMark)

def ExactRawDecorateEffectivity : Prop :=
  Primrec₂ paintStep ∧ Primrec paintFinish ∧ Primrec₂ decorateCode

def FullActualRawCanonicalNodeDecorator : Prop :=
  ExactRawDecorateCalibration ∧ ExactLiteralRawDecorationDomain ∧
    ExactCanonicalSuppliedDecoration ∧ ExactRawDecorateEffectivity

end LogicLineages.PermittedControl.ActualRawCanonicalNodeDecorator
