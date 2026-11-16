module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CalibrationProof
open GorbowSyntax GorbowPRProgram SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem logicalCalibration (f : Formula 1) (lhs rhs : Term 1) (old : Program 1)
 (hold : ∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) :
 ∀ v, evaluate (logical f lhs rhs old) v = HistoryDispatcher.logicalFunction v :=
 UniformClosedPropositional.StatementChecks.exactNativeRefinement _
  (CumulativeUniformRule12Source.CalibrationProof.logicalCalibration f lhs rhs old hold)
theorem arithmeticCalibration (a : Program 1)
 (ha : ∀ v, evaluate a v = HistoryDispatcher.arithmeticFunction v) :
 ∀ v, evaluate (arithmetic a) v = HistoryDispatcher.arithmeticFunction v :=
 CumulativeFullFormulaSource.CalibrationProof.arithmeticCalibration a ha
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CalibrationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CalibrationProof
