module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
/-- Whole encoded annotation argument list, not a fixed canonical pair. -/
def firstArg : Program 1 := HistoryLookup.head
def secondArg : Program 1 := applyOne HistoryLookup.head HistoryLookup.tail
def instantiated : Program 1 := applyTwo UniformClosedInstanceRecognizer.instanceCode firstArg secondArg
def instanceResult : Program 1 := applyOne HistoryCodec.predecessor instantiated
def quantified : Program 1 := applyTwo HistoryCodec.cons (constant 1 10) firstArg
def implication : Program 1 := applyTwo HistoryCodec.cons (constant 1 7)
 (applyTwo HistoryAppend.append quantified instanceResult)
/-- Exact original case13(0): wrong length and failed instance are None0;
success emits Some(binary7(unary10(firstArg),instance)). -/
def caseCode : Program 1 :=
 choose (applyTwo equalCode HistoryLengthOffset.lengthProgram (constant 1 2)) (constant 1 0)
  (choose instantiated (constant 1 0) (applyOne .succ implication))
def caseCall {ctx : Nat} (tag : Nat) (args : Term ctx) : Term ctx := call tag (args ::ᵥ nil)
def firstValue {ctx : Nat} (htag : Nat) (args : Term ctx) : Term ctx := call htag (args ::ᵥ nil)
def secondValue {ctx : Nat} (htag ttag : Nat) (args : Term ctx) : Term ctx :=
 call htag (call ttag (args ::ᵥ nil) ::ᵥ nil)
def instanceValue {ctx : Nat} (itag htag ttag : Nat) (args : Term ctx) : Term ctx :=
 UniformClosedInstanceRecognizer.instanceCall itag (firstValue htag args) (secondValue htag ttag args)
def formulaValue {ctx : Nat} (ctag atag : Nat) (formula result : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (Term.numeral 7)
  (HistoryAppend.appendCall atag (HistoryLookup.consCall ctag (Term.numeral 10) formula) result)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13
