module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Literal executable certificate constructor: [raw term,numeric value,input certificate]. -/
def producer : Program 3 := RawAdditionIteration.congruence (.projection 0)
 (applyOne LiteralNumeralPrefix.numeralCode (.projection 1)) (.projection 2)
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toEvaluation : RawUnaryEvaluation.Installation p old a x where
 producerTag : Nat
 hproducer : (nodes p)[producerTag]? = some ⟨3,producer⟩
def producerCall {ctx : Nat} (tag : Nat) (t m cert : Term ctx) : Term ctx := call tag (t ::ᵥ m ::ᵥ cert ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer
