module
public import LogicLineages.OrdinalComparison.ThetaEntryTargets
public import LogicLineages.OrdinalComparison.BinaryObserverTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.LinkedBoundaryParity.Targets
open LogicLineages.OrdinalComparison

/-- Supporting source equation delta, with actual linked unchanged-control inputs. -/
def ActualBoundaryParity : Prop :=
  ∀ v : Nat, 4 ≤ v →
    let u := Phi v
    let B := Phi u
    let C := Phi (u + 1)
    let e := u - 4
    let d := B - u + 3
    0 < d ∧ e + 4 = u ∧ d + e + 1 = B ∧ e ≤ C ∧
    actualOmegaCopyCount e u % 2 = (1 + restrictedPartitionCount d (C - e)) % 2 ∧
    actualOmegaCopyCount e u % 2 =
      (1 + (PowerSeries.coeff (C - e)
        (actualPolynomialSeriesQuotient (actualBinarySourceDenominator d)
          (1 : Polynomial (ZMod 2)))).val) % 2
end LogicLineages.CartierObserverCurrent.LinkedBoundaryParity.Targets
