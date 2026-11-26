module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector HistoryRuleSuffix
/-- Literal ORIGINAL equality syntax: formula token0 followed by the two term
prefix streams. Both templates undergo numeral substitution, not evaluation.
Templates are fixed before source selection; a future checker tag may be a
runtime template variable, without choosing a circular final source AST. -/
def equalityQuote {k : Nat} (t u : Term k) : Program k :=
 LiteralTemplateQuote.prependToken 0 (applyTwo HistoryAppend.append
  (LiteralTemplateQuote.templateQuote t) (LiteralTemplateQuote.templateQuote u))
def quoteCall {k ctx : Nat} (tag : Nat) (values : List.Vector (Term ctx) k) : Term ctx :=
 call tag values
/-- Task kind1 is the ORIGINAL formula grammar; it is distinct from term kind0. -/
def formulaTask {ctx : Nat} (ptag : Nat) (binder : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (Term.numeral 1) binder
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote
