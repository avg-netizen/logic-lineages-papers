module
public import LogicLineages.OrdinalComparison.RangePhiFactorization.CancellationProof
public import LogicLineages.OrdinalComparison.RangePhiFactorization.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePhiFactorization.StatementChecks

theorem fixed_predecessorHeadSyntax : Targets.PredecessorHeadSyntax := Proof.predecessorHeadSyntax
theorem fixed_headFactorization : Targets.HeadFactorization := Proof.headFactorization
theorem fixed_contextFactorization : Targets.ContextFactorization := Proof.contextFactorization
theorem fixed_phiHeadCancellation : Targets.PhiHeadCancellation := Proof.phiHeadCancellation
theorem fixed_factorPrograms : Targets.FactorPrograms := Proof.factorPrograms

#print axioms fixed_predecessorHeadSyntax
#print axioms fixed_headFactorization
#print axioms fixed_contextFactorization
#print axioms fixed_phiHeadCancellation
#print axioms fixed_factorPrograms

end LogicLineages.OrdinalComparison.RangePhiFactorization.StatementChecks
