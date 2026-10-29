module
public import LogicLineages.OrdinalComparison.OrdinalRepresentationTargets
public import Mathlib.SetTheory.Ordinal.CantorNormalForm

@[expose] public section

/-! Independent hereditary-CNF prerequisite for the actual source norm.

Paper 05, `foundations.tex`, lines 51–70: every ordinal below epsilon zero
has finite recursive Cantor normal form; `def:norm` charges each monomial
with its full positive finite coefficient. This target uses Mathlib's actual
ordinal CNF, not notation syntax, and imports no candidate proof.

Strict exponent descent is needed to define the source norm by actual ordinal
well-founded recursion. This prerequisite alone does not define that norm,
prove its representation correspondence, or assert encoded effectiveness.
-/

namespace LogicLineages.OrdinalComparison.Targets

def CNFDescentBelowEpsilonZero : Prop :=
  ∀ (a : Ordinal.{0}), a < epsilonZero →
    ∀ p ∈ Ordinal.CNF Ordinal.omega0 a,
      p.1 < a ∧ 0 < p.2 ∧ p.2 < Ordinal.omega0

end LogicLineages.OrdinalComparison.Targets
