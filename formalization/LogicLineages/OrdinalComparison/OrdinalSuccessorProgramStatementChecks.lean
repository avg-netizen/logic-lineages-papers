module
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.OrdinalSuccessorProgram.StatementChecks

theorem fixed_primitive : Targets.OrdinalSuccessorProgramsPrimitiveRecursive := primitive
theorem fixed_predecessor : Targets.ActualOrdinalSuccessorPredecessorProgram := predecessor
theorem fixed_classification : Targets.ActualOrdinalFiniteRemainderClassification := classification
theorem fixed_no_jump : Targets.ActualOrdinalSuccessorNoJump := no_jump

end LogicLineages.OrdinalComparison.OrdinalSuccessorProgram.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.OrdinalSuccessorProgram
