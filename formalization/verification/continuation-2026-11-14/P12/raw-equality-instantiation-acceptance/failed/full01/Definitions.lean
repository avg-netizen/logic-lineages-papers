module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Actual second annotation field of original [phi,u], not an extra operand. -/
def argumentCode : Program 1 := RawAddSucc.secondTermCode
def recognizer (a b : Term 1) : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (applyOne (RawEqualityInstantiation.line a b) argumentCode))
 (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator argumentCode)
def logicalLeaf (a b : Term 1) (old : Program 1) : Program 1 :=
 choose (recognizer a b) old (constant 1 1)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance
