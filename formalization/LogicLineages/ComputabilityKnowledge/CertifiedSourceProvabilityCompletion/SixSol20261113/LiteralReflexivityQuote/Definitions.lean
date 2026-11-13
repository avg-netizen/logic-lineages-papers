module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCode
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector HistoryRuleSuffix
/-- Exact ORIGINAL logical annotation for reflexivity: tag11 and a singleton
LIST OF term-prefix lists. The inner code is an element, not spliced as raw
list tokens. This is not a complete proof line or an accepted certificate. -/
def annotationQuote {k : Nat} (t : Term k) : Program k :=
 applyTwo HistoryCodec.pair (constant k 11)
  (applyTwo HistoryCodec.cons (LiteralTemplateQuote.templateQuote t) (constant k 0))
def quoteCall {k ctx : Nat} (tag : Nat) (values : List.Vector (Term ctx) k) : Term ctx :=
 call tag values
/-- Literal pair(tag11,singleton(rawTerm)); no rule/ref fields are added. -/
def annotationValue {ctx : Nat} (ptag ctag : Nat) (rawTerm : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (Term.numeral 11) (HistoryLookup.consCall ctag rawTerm .zero)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote
