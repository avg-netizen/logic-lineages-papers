module
public import LogicLineages.OrdinalComparison.SingleCoreRowProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreRowCompiler.StatementChecks

theorem fixed_parts_program : Targets.ActualSingleCoreRowPartsProgram := parts_program
theorem fixed_parts_semantics : Targets.ActualSingleCoreRowPartsSemantics := semantics
theorem fixed_sign : Targets.ActualSingleCoreFormalRowSign := sign
theorem fixed_full : Targets.FullActualSingleCoreFormalRow := full

#print axioms fixed_parts_program
#print axioms fixed_parts_semantics
#print axioms fixed_sign
#print axioms fixed_full

end LogicLineages.OrdinalComparison.SingleCoreRowCompiler.StatementChecks
