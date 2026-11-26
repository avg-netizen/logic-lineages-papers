module
public import LogicLineages.PermittedControl.LongFieldEffectiveTailTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-- Form tag, numerical answer/table sign, precise code of the lower-input
parameter field. Tag zero means constant; a nonzero tag means linear. -/
abbrev RawComparisonFormCode := Nat × Nat × LongFieldCode

def rawConstForm (c : Nat) : RawComparisonFormCode := (0,c,(0,0,0,0))

def rawLinearForm (sign : Nat) (H : LongFieldCode) : RawComparisonFormCode := (1,sign,H)

def encodeComparisonForm : ComparisonForm → RawComparisonFormCode
  | .const c => rawConstForm c
  | .linear sign H => rawLinearForm sign (longFieldCode H)

def rawDistinctForm (P Q : LongFieldCode) : RawComparisonFormCode :=
  let (tagP,a,lp,mp) := P
  let (tagQ,b,lq,mq) := Q
  if tagP = 0 then
    if tagQ = 0 then
      if a ≤ b then rawConstForm 0 else rawLinearForm 1 (0,a - b,0,0)
    else rawConstForm 0
  else if tagQ = 0 then
    if b ≤ a then rawLinearForm 1 (1,a - b,lp,mp)
    else rawLinearForm 1 (1,0,lp,ordinalAddCode mp (omegaMultipleTailCode (b - a)))
  else
    let mp' := ordinalAddCode mp (omegaMultipleTailCode (b - a))
    let mq' := ordinalAddCode mq (omegaMultipleTailCode (a - b))
    let dp := ordinalSubCode lp mp'
    let dq := ordinalSubCode lq mq'
    if rawComparisonCode dq dp = 0 then
      rawLinearForm (equalGapCertificateCode mp' mq' dq) (1,0,lp,ordinalAddCode mp' dq)
    else rawConstForm 0

def rawSameForm (P Q : LongFieldCode) : Nat :=
  let (tagP,a,lp,mp) := P
  let (tagQ,b,lq,mq) := Q
  if tagP = 0 then
    if tagQ = 0 then numericalComparison a b else 0
  else if tagQ = 0 then 2
  else
    let mp' := ordinalAddCode mp (omegaMultipleTailCode (b - a))
    let mq' := ordinalAddCode mq (omegaMultipleTailCode (a - b))
    let dp := ordinalSubCode lp mp'
    let dq := ordinalSubCode lq mq'
    let cmp := rawComparisonCode dp dq
    if cmp = 1 then equalGapCertificateCode mp' mq' dp else cmp

/-- Decode a tagged response to literal raw trees. Normality is not
silently assumed for arbitrary input codes and no semantic field value is
computed by this decoder. -/
abbrev DecodedRawField := Nat × Option (ONote × ONote)
abbrev DecodedRawComparisonForm := Sum Nat (Nat × DecodedRawField)

def rawFieldView : ValueField → DecodedRawField
  | .iterate a => (a,none)
  | .entry a lam mu => (a,some (lam.1,mu.1))

def rawComparisonFormView : ComparisonForm → DecodedRawComparisonForm
  | .const c => .inl c
  | .linear sign H => .inr (sign, rawFieldView H)

def decodeLongFieldCode (H : LongFieldCode) : DecodedRawField :=
  let (tag,a,lam,mu) := H
  (a, if tag = 0 then none else some (rawNoteDecode lam,rawNoteDecode mu))

def decodeRawComparisonForm (R : RawComparisonFormCode) : DecodedRawComparisonForm :=
  if R.1 = 0 then .inl R.2.1 else .inr (R.2.1,decodeLongFieldCode R.2.2)

/-- Both raw compilers are primitive recursive on all input codes. -/
def RawFieldComparisonFormEffective : Prop :=
  Primrec₂ rawDistinctForm ∧ Primrec₂ rawSameForm

/-- Exact agreement with the original syntax, both before and after raw
decoding. This is syntactic calibration on all encoded fields, not a
semantic claim that the old forms were correct on short entries. -/
def RawFieldComparisonFormCalibration : Prop :=
  (∀ H : ValueField, decodeLongFieldCode (longFieldCode H) = rawFieldView H) ∧
  (∀ R : ComparisonForm, decodeRawComparisonForm (encodeComparisonForm R) = rawComparisonFormView R) ∧
  ∀ F G : ValueField,
    rawDistinctForm (longFieldCode F) (longFieldCode G) = encodeComparisonForm (distinctForm F G) ∧
    decodeRawComparisonForm (rawDistinctForm (longFieldCode F) (longFieldCode G)) =
      rawComparisonFormView (distinctForm F G) ∧
    rawSameForm (longFieldCode F) (longFieldCode G) = sameForm F G

/-- Supporting raw output compiler only, leaving actual all-order
short/long assembly and low-input strips separate. -/
def FullRawFieldComparisonForm : Prop :=
  RawFieldComparisonFormEffective ∧ RawFieldComparisonFormCalibration

end LogicLineages.PermittedControl.FieldComparison
