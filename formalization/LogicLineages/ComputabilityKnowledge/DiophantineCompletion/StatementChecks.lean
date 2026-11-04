module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Proof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.StatementChecks
open Targets

theorem fixedPairDiophantine : PairDiophantine := Proof.pairDiophantine
theorem fixedUnpairDiophantine : UnpairDiophantine := Proof.unpairDiophantine
theorem fixedPartialPairClosure : PartialPairClosure := Proof.partialPairClosure
theorem fixedPartialCompositionClosure : PartialCompositionClosure := Proof.partialCompositionClosure
theorem fixedRecursionFreeGraphDiophantine : RecursionFreeGraphDiophantine :=
  Proof.recursionFreeGraphDiophantine
theorem fixedRecursionFreePolynomialRepresentation : RecursionFreePolynomialRepresentation :=
  Proof.recursionFreePolynomialRepresentation

#print axioms fixedPairDiophantine
#print axioms fixedUnpairDiophantine
#print axioms fixedPartialPairClosure
#print axioms fixedPartialCompositionClosure
#print axioms fixedRecursionFreeGraphDiophantine
#print axioms fixedRecursionFreePolynomialRepresentation
end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.StatementChecks
