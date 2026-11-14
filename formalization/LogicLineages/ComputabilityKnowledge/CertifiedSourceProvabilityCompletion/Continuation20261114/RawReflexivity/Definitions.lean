module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113
/-- One fixed program acts on raw encoded term syntax, not an external template.
It neither evaluates the term nor assumes its validity. -/
def lineConstructor : Program 1 :=
 TwoSol20261113.ReflexivityRecognizer.reflexiveLine (.projection 0)
def lineCall {ctx : Nat} (qtag : Nat) (raw : Term ctx) : Term ctx := call qtag (raw ::ᵥ nil)
def equalityValue {ctx : Nat} (ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero (HistoryAppend.appendCall atag raw raw)
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 LiteralReflexivityQuote.lineValue ptag ctag (equalityValue ctag atag raw) raw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity
