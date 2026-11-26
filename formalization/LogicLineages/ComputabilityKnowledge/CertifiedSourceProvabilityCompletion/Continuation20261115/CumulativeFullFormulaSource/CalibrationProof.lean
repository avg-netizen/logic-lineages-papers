module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.CalibrationProof
open GorbowSyntax GorbowPRProgram SixSol20261113
theorem logicalCalibration (f : Formula 1) (lhs rhs : Term 1) (old : Program 1)
 (hold : ∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) :
 ∀ v, evaluate (logical f lhs rhs old) v = HistoryDispatcher.logicalFunction v :=
 FullFormulaInstantiation.StatementChecks.exactNativeRefinement f _
  (CumulativeInstantiationSource.CalibrationProof.logicalCalibration lhs rhs old hold)
theorem arithmeticCalibration (a : Program 1)
 (ha : ∀ v, evaluate a v = HistoryDispatcher.arithmeticFunction v) :
 ∀ v, evaluate (arithmetic a) v = HistoryDispatcher.arithmeticFunction v :=
 CumulativeInstantiationSource.CalibrationProof.arithmeticCalibration a ha
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.CalibrationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.CalibrationProof
