module
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions

@[expose] public section

/-! Actual unary source collapse, paper 05 `foundations.tex`, `def:collapse`.

Use actual ordinal well-founded recursion and the actual norm-bounded set of
strict predecessors. The natural finite supremum includes zero by its bottom
convention. This is independent of the notation collapse; it is not a binary
budgeted surrogate. Values outside epsilon zero are totalized to zero and
have no source significance. No effectiveness or optimized recurrence claim
is made by this definition.
-/

namespace LogicLineages.OrdinalComparison

noncomputable def actualCollapse : Ordinal.{0} → Nat :=
  Ordinal.lt_wf.fix fun a rec =>
    if a < epsilonZero then
      (actualBoundedPredecessors a (Phi (actualOrdinalNorm a))).attach.sup
        (fun p => rec p.1 (by exact (Finset.mem_filter.mp p.2).2) + 1)
    else 0

end LogicLineages.OrdinalComparison
