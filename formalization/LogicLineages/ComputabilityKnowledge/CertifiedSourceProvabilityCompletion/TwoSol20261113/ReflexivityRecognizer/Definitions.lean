module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.LineStatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer
open GorbowPRProgram GorbowSyntax GorbowPRDefiningEquations List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
/-- Literal closed-term scanner, with original task kind0/context0. -/
def termTasks : Program 1 := applyTwo HistoryCodec.cons
 (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0)) (constant 1 0)
def termScan : Program 1 := applyTwo LiteralSyntaxScan.scanCode termTasks (.projection 0)
def termValidator : Program 1 := applyTwo equalCode termScan (constant 1 1)
def left (q : Program 1) : Program 1 := applyOne (HistoryDecoder.decoder false) q
def right (q : Program 1) : Program 1 := applyOne (HistoryDecoder.decoder true) q
def argsCode : Program 1 := left (right (right (right (right (.projection 0)))))
def termCode : Program 1 := applyOne HistoryLookup.head argsCode
/-- The original formula token0 followed by two identical term streams. -/
def reflexiveRaw (term : Program 1) : Program 1 := applyTwo HistoryCodec.cons (constant 1 0)
 (applyTwo HistoryAppend.append term term)
/-- Exact context0/tag0/tag11/singleton-args/zero-refs line. -/
def reflexiveLine (term : Program 1) : Program 1 :=
 applyTwo HistoryCodec.pair (constant 1 0)
  (applyTwo HistoryCodec.pair (reflexiveRaw term)
   (applyTwo HistoryCodec.pair (constant 1 0)
    (applyTwo HistoryCodec.pair (constant 1 11)
     (applyTwo HistoryCodec.pair (applyTwo HistoryCodec.cons term (constant 1 0))
      (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0))))))
/-- Match the entire unchanged line encoding, and genuinely validate its term. -/
def recognizer : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (reflexiveLine termCode))
 (applyOne termValidator termCode)
/-- Positive explicit reflexivity branch; every other input uses the prior leaf. -/
def logicalLeaf (old : Program 1) : Program 1 :=
 choose recognizer old (constant 1 1)
def leafCall {ctx : Nat} (tag : Nat) (line : Term ctx) : Term ctx := call tag (line ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer
