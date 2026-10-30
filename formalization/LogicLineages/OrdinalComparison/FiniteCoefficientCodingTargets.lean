module
public import LogicLineages.OrdinalComparison.FiniteCoefficientCodingDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def FiniteCoefficientCodingPrimitiveRecursive : Prop :=
  Primrec₂ finiteCoefficientSlope ∧ Primrec finiteCoefficientBase

def FiniteCoefficientSlopeCalibration : Prop :=
  (∀ B xs, finiteCoefficientSlope B xs=Nat.ofDigits B xs ∧
    finiteCoefficientSlope B xs=(xs.mapIdx fun i a => a*B^i).sum) ∧
  ∀ B : Nat, 2≤B → ∀ i : Nat, 0<B^i

/-- Equal vector lengths are necessary: trailing zero digits are not discarded. -/
def FiniteCoefficientFamilySeparation : Prop :=
  ∀ rows : List (List Nat),
    let B := finiteCoefficientBase rows
    2≤B ∧
    (∀ xs∈rows, ∀ a∈xs, a<B) ∧
    (∀ xs∈rows, ∀ ys∈rows, xs.length=ys.length →
      (finiteCoefficientSlope B xs=finiteCoefficientSlope B ys ↔ xs=ys))

end LogicLineages.OrdinalComparison.Targets
