module
public import LogicLineages.OrdinalComparison.ProfileDominatorDefinitions
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions
public import LogicLineages.OrdinalComparison.MaximumPredecessor

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 adjacent theorem, lines 538–546: actual affordable leading
certificate extracted from the executable exact maximum, not a chosen oracle.
The source later calls the lower suffix norm B; its actual norm is B−e and
its retained total is B. This supplier retains the literal norm budget. -/
def ActualAffordableLeadingMaximum : Prop :=
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell) →
    Ordinal.omega0 < L.1.repr → ∀ budget : Nat, 2 ≤ budget →
      let o := maximumPredecessor L budget
      let M := actualMaximumPredecessor L.1.repr budget
      let pi := (profileLeadingNote o).1.repr
      o.1.repr = M ∧ actualOrdinalNorm M = budget ∧
      Ordinal.omega0 ≤ M ∧ Ordinal.omega0 ≤ pi ∧ pi ≤ M ∧
      M < pi * Ordinal.omega0 ∧ pi < L.1.repr ∧ actualOrdinalNorm pi ≤ budget ∧
      (∃ beta : Ordinal.{0}, 0 < beta ∧ pi = Ordinal.omega0 ^ beta) ∧
      ∀ delta : Ordinal.{0}, Ordinal.omega0 ^ delta < L.1.repr →
        actualOrdinalNorm (Ordinal.omega0 ^ delta) ≤ budget → Ordinal.omega0 ^ delta ≤ pi

end LogicLineages.OrdinalComparison.Targets
