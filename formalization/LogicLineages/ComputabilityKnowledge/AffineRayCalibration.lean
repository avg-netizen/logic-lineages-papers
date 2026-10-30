module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodec

@[expose] public section

/-! The effective affine calibration used at the start and height-zero base
of paper02's finite-family ray lemma. The input is the collected finite list
of actual affine coefficient codes. The zero vector is always included in
the mathematical collection; adding it contributes no mass. The explicit
base exceeds every relevant coefficient difference, and all programs below
are ordinary natural-number/list operations without a comparison oracle.
-/
namespace LogicLineages.ComputabilityKnowledge.AffineRayCalibration

open ExponentialNormalForm ExponentialNormalFormCodec

def familyMass (family : List CoeffCode) : Nat :=
  family.foldr (fun c acc => c.foldr (fun x s => x + s) 0 + acc) 0

def rayBase (family : List CoeffCode) : Nat := 2 + 2 * familyMass family

def withZero (family : List CoeffCode) : List CoeffCode := [] :: family

def weights (d : Nat) (family : List CoeffCode) : List Nat :=
  (List.range d).map (fun i => rayBase family ^ i)

def slope (d : Nat) (family : List CoeffCode) (c : CoeffCode) : Nat :=
  (List.range d).foldr (fun i acc => c.getD (i + 1) 0 * rayBase family ^ i + acc) 0

def cutoff (family : List CoeffCode) : Nat := 2 * familyMass family + 1

def rayCompare (d : Nat) (family : List CoeffCode) (a b : CoeffCode) : Bool :=
  if slope d family a = slope d family b then decide (a.getD 0 0 < b.getD 0 0)
  else decide (slope d family a < slope d family b)

def rayTuple (d : Nat) (family : List CoeffCode) (t : Nat) : Fin d → Nat :=
  fun i => (weights d family).getD i.val 0 * t

end LogicLineages.ComputabilityKnowledge.AffineRayCalibration
