module
public import LogicLineages.PermittedControl.ThresholdDefinitions
public import LogicLineages.PermittedControl.OutputOffsetTargets
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

def ProperIntervalNotes (lambda mu : NONote) : Prop :=
  Order.IsSuccLimit lambda.1.repr ∧ (mu.1.repr=0 ∨ Order.IsSuccLimit mu.1.repr) ∧ mu.1.repr<lambda.1.repr

def ThresholdProgramsEffective : Prop :=
  Primrec (fun z : IntervalPairCodes×Nat => thresholdTailCode z.1 z.2) ∧
  Primrec (fun z : (IntervalPairCodes×SignedShiftCodes)×Nat => translatedThresholdTailCode z.1.1 z.1.2 z.2) ∧
  (∀ f : Nat → Nat, Computable f → Partrec (thresholdProgram f) ∧ Partrec (translatedThresholdProgram f)) ∧
  (∀ a b : Nat, signedComparisonCode a b=integerComparison (signedOffsetValue a) (signedOffsetValue b)) ∧
  (∀ c x : Nat, signedTranslateCode c x=((x:Int)+signedOffsetValue c).toNat) ∧
  (∀ c : Nat, signedOffsetMagnitudeCode c=(signedOffsetValue c).natAbs)

/-- Literal complete finite source descriptions, with genuine H-map results.
The unequal branches contain every printed comparison/equality cell. -/
def ActualThresholdDescription (f : Nat → Nat) (lp mp lq mq : NONote) (x y E F : Nat) : Prop :=
  let dp := lp.1.repr-mp.1.repr
  let dq := lq.1.repr-mq.1.repr
  let dpc := ordinalSubCode (rawNoteEncode lp.1) (rawNoteEncode mp.1)
  let dqc := ordinalSubCode (rawNoteEncode lq.1) (rawNoteEncode mq.1)
  (dp=dq → numericalComparison E F=
    (if x<y then 0 else if y<x then 2 else equalGapCertificateCode (rawNoteEncode mp.1) (rawNoteEncode mq.1) dpc)) ∧
  (dq<dp →
    let kappa := mp.1.repr+dq
    mp.1.repr<kappa ∧ kappa<lp.1.repr ∧
    ∃ i h : Nat, FirstEntry f (countInitial lp.1.repr x) kappa i ∧
      h=entryNormAt f (countInitial lp.1.repr x) i ∧
      (h,i) ∈ fixedEntryProgram f (rawNoteEncode lp.1,ordinalAddCode (rawNoteEncode mp.1) dqc,x) ∧
      InverseTableRows (equalGapCertificateCode (rawNoteEncode mp.1) (rawNoteEncode mq.1) dqc) y h F E) ∧
  (dp<dq →
    let kappa := mq.1.repr+dp
    mq.1.repr<kappa ∧ kappa<lq.1.repr ∧
    ∃ j h : Nat, FirstEntry f (countInitial lq.1.repr y) kappa j ∧
      h=entryNormAt f (countInitial lq.1.repr y) j ∧
      (h,j) ∈ fixedEntryProgram f (rawNoteEncode lq.1,ordinalAddCode (rawNoteEncode mq.1) dpc,y) ∧
      InverseTableRows (equalGapCertificateCode (rawNoteEncode mq.1) (rawNoteEncode mp.1) dpc) x h E F)

/-- Actual source decision, only on a proved computable tail. Every queried
fixed entry map and original comparison has actual first-hit semantics. -/
def ThresholdBaseCorrect : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lp mp lq mq : NONote), ProperIntervalNotes lp mp → ProperIntervalNotes lq mq →
  ∀ x y : Nat, thresholdTailCode (intervalPairCodes lp mp lq mq) B≤x →
    thresholdTailCode (intervalPairCodes lp mp lq mq) B≤y →
  ∃ i j : Nat, FirstEntry f (countInitial lp.1.repr x) mp.1.repr i ∧
    FirstEntry f (countInitial lq.1.repr y) mq.1.repr j ∧
    let E := entryNormAt f (countInitial lp.1.repr x) i
    let F := entryNormAt f (countInitial lq.1.repr y) j
    (thresholdProgram f (intervalPairCodes lp mp lq mq,(x,y))).Dom ∧
    (∀ c : Nat, c ∈ thresholdProgram f (intervalPairCodes lp mp lq mq,(x,y)) ↔ c=numericalComparison E F) ∧
    ActualThresholdDescription f lp mp lq mq x y E F

/-- Literal signed translations and output offsets, with genuine computation,
all collisions and nontruncation paid by the displayed effective larger tail. -/
def TranslatedThresholdCorrect : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lp mp lq mq : NONote), ProperIntervalNotes lp mp → ProperIntervalNotes lq mq →
  ∀ (s : SignedShiftCodes) (x y : Nat),
    translatedThresholdTailCode (intervalPairCodes lp mp lq mq) s B≤x →
    translatedThresholdTailCode (intervalPairCodes lp mp lq mq) s B≤y →
    let u := ((x:Int)+signedOffsetValue s.1.1).toNat
    let v := ((y:Int)+signedOffsetValue s.1.2).toNat
    0≤(x:Int)+signedOffsetValue s.1.1 ∧ 0≤(y:Int)+signedOffsetValue s.1.2 ∧
    ∃ i j : Nat, FirstEntry f (countInitial lp.1.repr u) mp.1.repr i ∧
      FirstEntry f (countInitial lq.1.repr v) mq.1.repr j ∧
      (translatedThresholdProgram f ((intervalPairCodes lp mp lq mq,s),(x,y))).Dom ∧
      (∀ c : Nat, c ∈ translatedThresholdProgram f ((intervalPairCodes lp mp lq mq,s),(x,y)) ↔
        c=integerComparison ((entryNormAt f (countInitial lp.1.repr u) i:Int)+signedOffsetValue s.2.1)
          ((entryNormAt f (countInitial lq.1.repr v) j:Int)+signedOffsetValue s.2.2))

/-- Full source prop:threshold, including effective fixed normal endpoints,
actual finite-decision program/tails and all signed shifts/collisions. -/
def FullThreshold : Prop := ThresholdProgramsEffective ∧ ThresholdBaseCorrect ∧
  TranslatedThresholdCorrect ∧ SignedOffsetTailEffective

end LogicLineages.PermittedControl.Targets
