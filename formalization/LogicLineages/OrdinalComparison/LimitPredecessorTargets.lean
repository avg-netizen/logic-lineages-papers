module
public import LogicLineages.OrdinalComparison.PredecessorTargets

@[expose] public section

/-! Independent statement of paper 05, `lem:saturation`. A nonzero limit is
expressed by the standard `Order.IsSuccLimit` predicate on the actual ordinal
denotation, rather than by a syntactic surrogate. -/

namespace LogicLineages.OrdinalComparison.Targets

def LimitMaximumPredecessorSaturation (M : NONote → Nat → NONote) : Prop :=
  ∀ a : NONote, Order.IsSuccLimit a.1.repr → ∀ budget : Nat,
    Vendor.R1.treeWeight (M a budget).1 = budget

def LimitMaximumPredecessorStrictGrowth (M : NONote → Nat → NONote) : Prop :=
  ∀ a : NONote, Order.IsSuccLimit a.1.repr → StrictMono (M a)

end LogicLineages.OrdinalComparison.Targets
