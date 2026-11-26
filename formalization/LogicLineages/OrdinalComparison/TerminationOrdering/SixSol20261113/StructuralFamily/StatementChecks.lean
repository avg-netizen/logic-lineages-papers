module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.FailureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.StatementChecks
theorem coherent : Targets.ConcreteFamilyCoherent := FamilyProof.coherent
theorem concreteFailure : Targets.ConcreteScannerFailure := FailureProof.concrete
theorem genericFailure : Targets.GenericScannerFailure := FailureProof.generic
end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.StatementChecks
