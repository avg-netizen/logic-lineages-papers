module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix
/-- Fixed original unary term AST; input is an arbitrary raw closed term code,
not its value and not a numeral count. Original prefix tokens are unchanged. -/
def program : Term 1 → Program 1
 | .var _ => .projection 0
 | .zero => applyTwo HistoryCodec.cons (constant 1 1) (constant 1 0)
 | .succ t => applyTwo HistoryCodec.cons (constant 1 2) (program t)
 | .add t u => applyTwo HistoryCodec.cons (constant 1 3) (applyTwo HistoryAppend.append (program t) (program u))
 | .mul t u => applyTwo HistoryCodec.cons (constant 1 4) (applyTwo HistoryAppend.append (program t) (program u))
 | .universalFunction t => applyTwo HistoryCodec.cons (constant 1 5) (program t)
def value {ctx : Nat} (ctag atag : Nat) (raw : Term ctx) : Term 1 → Term ctx
 | .var _ => raw
 | .zero => HistoryLookup.consCall ctag (Term.numeral 1) .zero
 | .succ t => HistoryLookup.consCall ctag (Term.numeral 2) (value ctag atag raw t)
 | .add t u => HistoryLookup.consCall ctag (Term.numeral 3)
   (HistoryAppend.appendCall atag (value ctag atag raw t) (value ctag atag raw u))
 | .mul t u => HistoryLookup.consCall ctag (Term.numeral 4)
   (HistoryAppend.appendCall atag (value ctag atag raw t) (value ctag atag raw u))
 | .universalFunction t => HistoryLookup.consCall ctag (Term.numeral 5) (value ctag atag raw t)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution
