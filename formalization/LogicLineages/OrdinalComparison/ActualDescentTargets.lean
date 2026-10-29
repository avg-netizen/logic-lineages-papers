module
public import LogicLineages.OrdinalComparison.ActualDescentDefinitions

@[expose] public section

/-! Independent full-domain split and step obligations for paper 05,
`cor:closed-evaluation` and the norm update in `thm:complete-count`.

These assertions concern every nonfinite actual ordinal below epsilon zero,
with ordinary ordinal operations and independently defined norm/collapse/maximum.
They import no new property proof. They do not assert a faithful finite-code
encoding or Mathlib Computable certificate; that obligation remains separate.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualNonfiniteDecomposition : Prop :=
  ∀ a : Ordinal.{0}, Ordinal.omega0 ≤ a → a < epsilonZero →
    actualLimitPart a < epsilonZero ∧ Order.IsSuccLimit (actualLimitPart a) ∧
      a = actualLimitPart a + (actualTailPart a : Ordinal) ∧
      actualOrdinalNorm a = actualOrdinalNorm (actualLimitPart a) + actualTailPart a

def ActualDescentStepStrict : Prop :=
  ∀ a : Ordinal.{0}, Ordinal.omega0 ≤ a → a < epsilonZero → actualDescentStep a < a

def ActualDescentStepCollapse : Prop :=
  ∀ a : Ordinal.{0}, Ordinal.omega0 ≤ a → a < epsilonZero →
    actualCollapse a = actualCollapse (actualDescentStep a) + 1

def ActualDescentStepNorm : Prop :=
  ∀ a : Ordinal.{0}, Ordinal.omega0 ≤ a → a < epsilonZero →
    actualOrdinalNorm (actualDescentStep a) = Phi (actualOrdinalNorm a)

end LogicLineages.OrdinalComparison.Targets
