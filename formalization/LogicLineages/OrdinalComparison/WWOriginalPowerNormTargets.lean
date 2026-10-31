module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-! Actual-ordinal exponent/norm suppliers from original Proposition2.2(3).
The exponent is genuine ordinal exponentiation; all norms are actual hereditary
CNF norms. These statements are not syntactic input/output size bounds. -/
def ActualOmegaLeftNormBounds : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    actualOrdinalNorm a ≤ actualOrdinalNorm (Ordinal.omega0 * a) ∧
    actualOrdinalNorm (Ordinal.omega0 * a) ≤ 2 * actualOrdinalNorm a

def ActualBaseTwoPowerNormFormula : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → ∀ k : Nat,
    actualOrdinalNorm ((2 : Ordinal) ^ (Ordinal.omega0 * a + (k : Ordinal))) =
      2 ^ k * (1 + actualOrdinalNorm a)

def ActualBaseTwoInverseNorm : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    actualOrdinalNorm a ≤ 2 * actualOrdinalNorm ((2 : Ordinal) ^ a)

def ActualBaseTwoForwardNorm : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    actualOrdinalNorm ((2 : Ordinal) ^ a) ≤ 2 ^ actualOrdinalNorm a

end LogicLineages.OrdinalComparison.Source.Targets
