module
public import LogicLineages.OrdinalComparison.TerminationOrdering.HeadClosureProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.StatementChecks

theorem fixedRenamingHeadClosure : Targets.RenamingHeadClosure :=
  Proof.renamingHeadClosure
theorem fixedMarkingHeadClosure : Targets.MarkingHeadClosure :=
  Proof.markingHeadClosure
theorem fixedSubstitutionHeadClosure : Targets.SubstitutionHeadClosure :=
  Proof.substitutionHeadClosure
theorem fixedSimultaneousApplicationHeadClosure : Targets.SimultaneousApplicationHeadClosure :=
  Proof.simultaneousApplicationHeadClosure

end LogicLineages.OrdinalComparison.TerminationOrdering.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering
