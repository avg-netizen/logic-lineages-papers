module
public import LogicLineages.PermittedControl.RelativeNormDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- CNF-restricted ordinal has exactly the retained norm contributions. -/
def RelativePrefixNorm : Prop := ∀ (mu e : Ordinal.{0}), mu < epsilonZero →
  relativePrefix mu e < epsilonZero ∧
  relativeProfile mu e =
    (((Ordinal.CNF Ordinal.omega0 mu).filter (fun p => e ≤ p.1)).map
      (fun p => p.2.card.toNat * (1 + actualOrdinalNorm p.1))).sum ∧
  relativeProfile mu e ≤ actualOrdinalNorm mu

/-- Complete eq:relative-norm, including zero and arbitrary absorption.
No prefix-compatibility or profile supplier is assumed. -/
def RelativeNorm : Prop := ∀ (mu y : Ordinal.{0}), mu < epsilonZero → y < epsilonZero →
  actualOrdinalNorm (mu + y) = actualOrdinalNorm y + relativeCost mu y ∧
  0 ≤ relativeCost mu y ∧ relativeCost mu y ≤ actualOrdinalNorm mu

end LogicLineages.PermittedControl.Targets
