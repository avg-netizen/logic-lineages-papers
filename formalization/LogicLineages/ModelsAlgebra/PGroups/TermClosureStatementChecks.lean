module

public import LogicLineages.ModelsAlgebra.PGroups.TermClosure
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_term_closure_membership : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTermClosureMembership :=
  LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth.term_closure_membership

theorem fixed_closure_term_representation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupClosureTermRepresentation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth.closure_term_representation

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
