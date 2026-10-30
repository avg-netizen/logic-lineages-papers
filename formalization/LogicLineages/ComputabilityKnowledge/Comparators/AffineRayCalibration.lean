module

public import LogicLineages.ComputabilityKnowledge.AffineRayCalibration

@[expose] public section

/-! Exact effective source-ray calibration supplier, paper02 lem:ray first
two proof paragraphs. Source finite coefficient vectors retain their constant
slot; the injected slope uses only variable slots. The full higher-height
ray-induction theorem is not assumed or claimed by this affine base target.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.AffineRayCalibration

open ExponentialNormalForm ExponentialNormalFormCodec
open LogicLineages.ComputabilityKnowledge.AffineRayCalibration

def PositiveCalibration : Prop :=
  ∀ (d : Nat) (family : List CoeffCode),
    2 ≤ rayBase family ∧ (weights d family).length = d ∧ 0 < cutoff family ∧
    (∀ i : Fin d, (weights d family).getD i.val 0 = rayBase family ^ i.val ∧
      0 < (weights d family).getD i.val 0) ∧
    (∀ c ∈ withZero family, ∀ i : Fin (d + 1), coeffDecode d c i < rayBase family)

def SlopeCalibration : Prop :=
  ∀ (d : Nat) (family : List CoeffCode),
    (∀ c : CoeffCode, slope d family c =
      ∑ i : Fin d, coeffDecode d c i.succ * (weights d family).getD i.val 0) ∧
    ∀ a ∈ withZero family, ∀ b ∈ withZero family,
      (slope d family a = slope d family b ↔
        ∀ i : Fin d, coeffDecode d a i.succ = coeffDecode d b i.succ)

def AffineRayEvaluation : Prop :=
  ∀ (d : Nat) (family : List CoeffCode) (c : CoeffCode) (t : Nat),
    affineValue (coeffDecode d c) (rayTuple d family t) = c.getD 0 0 + slope d family c * t

def ComputedEventualComparison : Prop :=
  ∀ (d : Nat) (family : List CoeffCode),
    ∀ a ∈ withZero family, ∀ b ∈ withZero family, ∀ t, cutoff family ≤ t →
      (rayCompare d family a b = true ↔
        affineValue (coeffDecode d a) (rayTuple d family t) <
          affineValue (coeffDecode d b) (rayTuple d family t)) ∧
      (affineValue (coeffDecode d a) (rayTuple d family t) =
          affineValue (coeffDecode d b) (rayTuple d family t) ↔
        coeffDecode d a = coeffDecode d b) ∧
      (∀ i : Fin d, 0 < rayTuple d family t i)

def ConstantFreeGap : Prop :=
  ∀ (d : Nat) (family : List CoeffCode), ∀ a ∈ withZero family, ∀ b ∈ withZero family,
    a.getD 0 0 = 0 → b.getD 0 0 = 0 → coeffDecode d a ≠ coeffDecode d b →
    ∀ t : Nat,
      (rayCompare d family a b = true →
        affineValue (coeffDecode d a) (rayTuple d family t) + t ≤
          affineValue (coeffDecode d b) (rayTuple d family t)) ∧
      (rayCompare d family a b = false →
        affineValue (coeffDecode d b) (rayTuple d family t) + t ≤
          affineValue (coeffDecode d a) (rayTuple d family t))

def ActualPrimitivePrograms : Prop :=
  Primrec (fun p : Nat × List CoeffCode => weights p.1 p.2) ∧
  Primrec cutoff ∧
  Primrec (fun p : Nat × List CoeffCode × CoeffCode => slope p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List CoeffCode × CoeffCode × CoeffCode =>
    rayCompare p.1 p.2.1 p.2.2.1 p.2.2.2)

def Target : Prop := PositiveCalibration ∧ SlopeCalibration ∧ AffineRayEvaluation ∧
  ComputedEventualComparison ∧ ConstantFreeGap ∧ ActualPrimitivePrograms

end LogicLineages.ComputabilityKnowledge.Comparators.AffineRayCalibration
