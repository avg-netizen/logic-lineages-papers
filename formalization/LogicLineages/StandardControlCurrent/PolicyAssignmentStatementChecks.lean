module
public import LogicLineages.StandardControlCurrent.PolicyAssignmentSyntaxProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentRunPrograms
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks
theorem full : PolicyAssignmentTargets.Full :=
  ⟨PolicyAssignmentSyntaxProof.literal,PolicyAssignmentSyntaxProof.sourceExact,
    PolicyAssignmentSyntaxProof.success,fun p hp =>
      ⟨PolicyAssignmentBasePrograms.prime p hp,PolicyAssignmentRunPrograms.assignment p hp⟩⟩
#print axioms full
end LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks
