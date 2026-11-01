module
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteKernelRecursion.StatementChecks

theorem fixed_block : Targets.ActualFiniteKernelBlockRecursion := block
theorem fixed_signed : Targets.ActualFiniteSignedBlockRecursion := signed_block
theorem fixed_quadratic : Targets.ActualFiniteQuadraticShift := quadratic
theorem fixed_programs : Targets.ActualFiniteKernelPrograms := programs
theorem fixed_obstruction : Targets.ActualSignedDegreeTwoRecursionObstruction := obstruction

#print axioms fixed_block
#print axioms fixed_signed
#print axioms fixed_quadratic
#print axioms fixed_programs
#print axioms fixed_obstruction

end LogicLineages.OrdinalComparison.FiniteKernelRecursion.StatementChecks
