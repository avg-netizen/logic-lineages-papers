module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
/-- Fixed whole-argument-list AST, independent of formula codes and root tags. -/
def firstArg : Program 1 := HistoryLookup.head
def secondArg : Program 1 := applyOne HistoryLookup.head HistoryLookup.tail
def thirdArg : Program 1 := applyOne HistoryLookup.head (applyOne HistoryLookup.tail HistoryLookup.tail)
def leftInstance : Program 1 := applyTwo UniformClosedInstanceRecognizer.instanceCode firstArg secondArg
def rightInstance : Program 1 := applyTwo UniformClosedInstanceRecognizer.instanceCode firstArg thirdArg
def leftResult : Program 1 := applyOne HistoryCodec.predecessor leftInstance
def rightResult : Program 1 := applyOne HistoryCodec.predecessor rightInstance
def equality : Program 1 := applyTwo HistoryCodec.cons (constant 1 0)
 (applyTwo HistoryAppend.append secondArg thirdArg)
def consequent : Program 1 := applyTwo HistoryCodec.cons (constant 1 7)
 (applyTwo HistoryAppend.append leftResult rightResult)
def implication : Program 1 := applyTwo HistoryCodec.cons (constant 1 7)
 (applyTwo HistoryAppend.append equality consequent)
/-- Original case12(0), including length rejection and both Option failures. -/
def caseCode : Program 1 :=
 choose (applyTwo equalCode HistoryLengthOffset.lengthProgram (constant 1 3)) (constant 1 0)
  (choose leftInstance (constant 1 0)
   (choose rightInstance (constant 1 0) (applyOne .succ implication)))
def caseCall {ctx : Nat} (tag : Nat) (args : Term ctx) : Term ctx := call tag (args ::ᵥ nil)
def firstValue {ctx : Nat} (htag : Nat) (args : Term ctx) : Term ctx := call htag (args ::ᵥ nil)
def secondValue {ctx : Nat} (htag ttag : Nat) (args : Term ctx) : Term ctx :=
 call htag (call ttag (args ::ᵥ nil) ::ᵥ nil)
def thirdValue {ctx : Nat} (htag ttag : Nat) (args : Term ctx) : Term ctx :=
 call htag (call ttag (call ttag (args ::ᵥ nil) ::ᵥ nil) ::ᵥ nil)
def leftValue {ctx : Nat} (itag htag ttag : Nat) (args : Term ctx) : Term ctx :=
 UniformClosedInstanceRecognizer.instanceCall itag (firstValue htag args) (secondValue htag ttag args)
def rightValue {ctx : Nat} (itag htag ttag : Nat) (args : Term ctx) : Term ctx :=
 UniformClosedInstanceRecognizer.instanceCall itag (firstValue htag args) (thirdValue htag ttag args)
def formulaValue {ctx : Nat} (ctag atag : Nat) (t u left right : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.binaryValue ctag atag 7
  (FixedFormulaSubstitution.binaryValue ctag atag 0 t u)
  (FixedFormulaSubstitution.binaryValue ctag atag 7 left right)
def decodedArguments (code : Nat) : List (List Nat) :=
 (Encodable.decode (α := List (List Nat)) code).getD []
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12
