module
public import LogicLineages.OrdinalComparison.Definitions

@[expose] public section

/-! Independent greatest-predecessor specification. It imports neither the
enumeration nor the maximum implementation. The source domain is `a > 0`. -/

namespace LogicLineages.OrdinalComparison.Targets

def MaximumPredecessorCorrect (M : NONote → Nat → NONote) : Prop :=
  ∀ (a : NONote) (budget : Nat), 0 < a →
    IsGreatest {b : NONote | b < a ∧ Vendor.R1.treeWeight b.1 ≤ budget}
      (M a budget)

def FiniteMaximumPredecessor (M : NONote → Nat → NONote) : Prop :=
  ∀ n budget : Nat,
    M (NONote.ofNat (n + 1)) budget = NONote.ofNat (min n budget)

end LogicLineages.OrdinalComparison.Targets
