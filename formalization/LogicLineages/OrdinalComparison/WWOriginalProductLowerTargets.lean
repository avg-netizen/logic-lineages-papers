module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions
public import LogicLineages.OrdinalComparison.NaturalArithmeticDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-! Actual-ordinal positive product lower estimates from the original
Proposition 2.2, used in the repaired first-free-subterm norm argument.
All positivity and below-epsilon-zero hypotheses are source hypotheses.
No exponential inverse-norm estimate or full delta bound is assumed. -/
def ActualPositiveOrdinalNorm : Prop :=
  ∀ a : Ordinal.{0}, 0 < a → a < epsilonZero → 0 < actualOrdinalNorm a

def ActualNaturalProductNormLower : Prop :=
  ∀ a b : Ordinal.{0}, 0 < a → 0 < b → a < epsilonZero → b < epsilonZero →
    actualOrdinalNorm a + actualOrdinalNorm b - 1 ≤ actualOrdinalNorm (ordinalNaturalProduct a b)

def ActualNaturalProductComponentNorm : Prop :=
  ∀ a b : Ordinal.{0}, 0 < a → 0 < b → a < epsilonZero → b < epsilonZero →
    actualOrdinalNorm a ≤ actualOrdinalNorm (ordinalNaturalProduct a b) ∧
    actualOrdinalNorm b ≤ actualOrdinalNorm (ordinalNaturalProduct a b)

end LogicLineages.OrdinalComparison.Source.Targets
