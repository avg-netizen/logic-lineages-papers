module
public import LogicLineages.OrdinalComparison.Definitions

@[expose] public section

/-! Independent finite-tail specification used by paper 05's saturation and
single-predecessor arguments. Addition in the denotation below is ordinary
ordinal addition; its finite-tail norm formula is stated separately. -/

namespace LogicLineages.OrdinalComparison.Targets

def FiniteTailCorrect (tail : NONote → Nat → NONote) : Prop :=
  ∀ (a : NONote) (n : Nat),
    (tail a n).1.repr = a.1.repr + (n : Ordinal) ∧
    Vendor.R1.treeWeight (tail a n).1 = Vendor.R1.treeWeight a.1 + n

end LogicLineages.OrdinalComparison.Targets
