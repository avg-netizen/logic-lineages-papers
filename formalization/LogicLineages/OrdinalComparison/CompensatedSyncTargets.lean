module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Genuine two-mass synchronized comparison for paper07 adjacent separation.
Both suffix and total inequalities are retained: pointwise comparison of the
compensated control functions alone is neither assumed nor asserted. -/
def ActualCompensatedBudgetPreservation : Prop :=
  ∀ a b x y : Nat, x ≤ y → a + x ≤ b + y →
    compensatedPrefixControl a x ≤ compensatedPrefixControl b y ∧
    a + compensatedPrefixControl a x ≤ b + compensatedPrefixControl b y

def ActualCompensatedSynchronizedTraces : Prop :=
  ∀ a b : Nat, ∀ A B : Ordinal.{0}, A ≤ B → B < epsilonZero →
    actualOrdinalNorm A ≤ actualOrdinalNorm B →
    a + actualOrdinalNorm A ≤ b + actualOrdinalNorm B →
      let g := compensatedPrefixControl a
      let h := compensatedPrefixControl b
      let C := actualControlledCount g A
      let D := actualControlledCount h B
      C ≤ D ∧
      (∀ i : Nat, i ≤ C →
        actualControlledStateAfter g A i ≤ actualControlledStateAfter h B i ∧
        actualOrdinalNorm (actualControlledStateAfter g A i) ≤
          actualOrdinalNorm (actualControlledStateAfter h B i) ∧
        a + actualOrdinalNorm (actualControlledStateAfter g A i) ≤
          b + actualOrdinalNorm (actualControlledStateAfter h B i)) ∧
      a + actualOrdinalNorm (actualControlledStateAfter g A C) ≤
        b + actualOrdinalNorm (actualControlledStateAfter h B D)

end LogicLineages.OrdinalComparison.Targets
