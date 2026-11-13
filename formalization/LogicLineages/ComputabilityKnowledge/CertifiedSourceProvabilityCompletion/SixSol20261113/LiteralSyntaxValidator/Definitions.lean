module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector HistoryRuleSuffix
/-- Fresh literal formula validator on [binder context, raw-token-list code].
Equality is tested against SOME empty, whose exact original encoding is1.
This does not identify the existential validity leaf of an earlier source. -/
def formulaTask : Program 2 :=
 applyTwo HistoryCodec.pair (constant 2 1) (.projection 0)
def formulaTasks : Program 2 :=
 applyTwo HistoryCodec.cons formulaTask (constant 2 0)
def formulaScan : Program 2 :=
 applyTwo LiteralSyntaxScan.scanCode formulaTasks (.projection 1)
def formulaValidator : Program 2 :=
 applyTwo equalCode formulaScan (constant 2 1)
/-- Actual literal Line projection: pair(context,pair(raw,remaining fields)).
No rule or payload condition is imposed by this validity leaf. -/
def lineContext : Program 1 := HistoryDecoder.decoder false
def lineRaw : Program 1 :=
 applyOne (HistoryDecoder.decoder false) (HistoryDecoder.decoder true)
def lineValidator : Program 1 :=
 applyTwo formulaValidator lineContext lineRaw

def formulaCall {ctx : Nat} (tag : Nat) (context raw : Term ctx) : Term ctx :=
 call tag (context ::ᵥ raw ::ᵥ nil)
def lineCall {ctx : Nat} (tag : Nat) (line : Term ctx) : Term ctx :=
 call tag (line ::ᵥ nil)
def binaryRaw {ctx : Nat} (atag ctag : Nat) (token : Nat) (left right : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (Term.numeral token) (HistoryAppend.appendCall atag left right)
def quantifiedRaw {ctx : Nat} (ctag : Nat) (token : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (Term.numeral token) raw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator
