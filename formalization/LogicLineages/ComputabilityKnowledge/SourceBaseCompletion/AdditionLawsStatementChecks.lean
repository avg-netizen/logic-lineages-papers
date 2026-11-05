module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLawsTargets
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLawsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLaws.StatementChecks

theorem associativity : Targets.Associativity := Proof.associativity
theorem commutativity : Targets.Commutativity := Proof.commutativity
theorem leftZeroOfSumZero : Targets.LeftZeroOfSumZero := Proof.leftZeroOfSumZero
theorem additionLaws : Targets.Target := Proof.fullTarget

#print axioms associativity
#print axioms commutativity
#print axioms leftZeroOfSumZero
#print axioms additionLaws

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLaws.StatementChecks
