module
public import LogicLineages.OrdinalComparison.MaximumPredecessor
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.CheckedPredecessor

theorem greatest_among_all_normal_predecessors :
    Targets.MaximumPredecessorCorrect maximumPredecessor := maximumPredecessor_correct

theorem exact_finite_predecessor_formula :
    Targets.FiniteMaximumPredecessor maximumPredecessor := maximumPredecessor_finite

end LogicLineages.OrdinalComparison.CheckedPredecessor

#audit_namespace LogicLineages.OrdinalComparison
