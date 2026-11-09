module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.ClosedPackageProof
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.CodeCalibrationProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineCorrectnessProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.DecisionProof
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample

/-- Apply the actual closed-word program at the actual emitted degree. -/
theorem actualPackageDecision : Targets.ActualPackageDecision := by
  intro p hp
  unfold packageCounterexample
  rw [CodeProof.literalCodeCalibration]
  exact (ClosedWordDecisionCompletion.MachineProof.actualClosedDecision p.1.1 (matrix p)
    (MatrixProof.exactMatrixSyntax p hp).1).trans (MatrixProof.exactClosedPackage p hp).symm

/-- Numeric rejection is retained, without a semantic claim outside the
original internally level-bounded source class. -/
theorem exactSourceDomain : Targets.ExactSourceDomain := by
  intro q
  constructor
  · simpa only [decision,Option.isSome_map] using (AdmissionProof.exactGuardedDomain q).1
  · intro h
    have hn := (AdmissionProof.exactGuardedDomain q).2.1 h
    simp [decision,solve,hn]

theorem decision_of_package (q : SourceCode.Input) (p : Pair.Package)
    (hp : Admission.compile q = some p) :
    decision q = some (!(packageCounterexample p)) ∧
    solve q = !(packageCounterexample p) := by
  simp [decision,solve,hp]

#print axioms actualPackageDecision
#print axioms exactSourceDomain
#print axioms decision_of_package

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.DecisionProof
