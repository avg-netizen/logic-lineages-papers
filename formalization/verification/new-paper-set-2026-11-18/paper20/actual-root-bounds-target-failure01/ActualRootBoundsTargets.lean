module
public import LogicLineages.OrdinalComparison.RealResidueBoundsTargets

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ActualRootBounds.Targets
open LogicLineages.OrdinalComparison

/-- Full current20 lem:bounds: actual linked inputs, integer difference,
ordinary real quotient, and genuine real exponent 2r/3. -/
def CompleteActualBounds : Prop := ∀ v : Nat, 4 ≤ v →
  let u := Phi v
  let B := Phi u
  let r := Nat.log 2 B - 1
  let q := 2 ^ r + 1
  let m := u - 2
  let delta := m * (m + 1) / 2
  let e := u - 4
  96 ≤ r ∧ delta < r ∧
  (0 : Int) < (delta : Int) - 2 * (e : Int) ∧
  (delta : Int) - 2 * (e : Int) < (q : Int) ∧
  (2 : Real) ^ r / ((r : Real) + 1) < (Nat.totient q : Real) ∧
  Real.rpow 2 (2 * (r : Real) / 3) * (delta : Real) <
    (2 : Real) ^ r / ((r : Real) + 1)
end LogicLineages.CartierObserverCurrent.ActualRootBounds.Targets
