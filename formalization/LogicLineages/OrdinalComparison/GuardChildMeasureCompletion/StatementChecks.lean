module
public import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.ChildrenProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.StatementChecks

theorem fixed_measureWellFounded : Targets.MeasureWellFounded := Proof.measureWellFounded
theorem fixed_countCriterion : Targets.CountCriterion := Proof.countCriterion
theorem fixed_measureInvariance : Targets.MeasureInvariance := Proof.measureInvariance
theorem fixed_admissionRankBound : Targets.AdmissionRankBound := Proof.admissionRankBound
theorem fixed_actualGuardChildDecrease : Targets.ActualGuardChildDecrease := Proof.actualGuardChildDecrease
theorem fixed_actualGuardChildWellFounded : Targets.ActualGuardChildWellFounded := Proof.actualGuardChildWellFounded

#print axioms fixed_measureWellFounded
#print axioms fixed_countCriterion
#print axioms fixed_measureInvariance
#print axioms fixed_admissionRankBound
#print axioms fixed_actualGuardChildDecrease
#print axioms fixed_actualGuardChildWellFounded

end LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.StatementChecks
