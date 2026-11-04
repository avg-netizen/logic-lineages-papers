module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseTargets
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.StatementChecks

theorem fullPAAvailability : Targets.FullPAAvailability := Proof.fullPAAvailability
theorem actualSyntaxAdequacy : Targets.ActualSyntaxAdequacy := Proof.actualSyntaxAdequacy
theorem baseRevisionValidity : Targets.BaseRevisionValidity := Proof.baseRevisionValidity
theorem selfIndexedCalibration : Targets.SelfIndexedCalibration := Proof.selfIndexedCalibration
theorem completeSourcePair : Targets.CompleteSourcePair := Proof.completeSourcePair
theorem sourceBaseCompletion : Targets.Target := Proof.fullTarget

#print axioms fullPAAvailability
#print axioms actualSyntaxAdequacy
#print axioms baseRevisionValidity
#print axioms selfIndexedCalibration
#print axioms completeSourcePair
#print axioms sourceBaseCompletion

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.StatementChecks
