module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowProofChecker
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote
open GorbowSyntax GorbowPRProgram HistoryRuleSuffix
/-- Original closed logical reflexivity line, including canonical zero rule
and reference fields. Payload is (11,[term prefix],0,0), not a paired annotation. -/
def lineQuote {k : Nat} (t : Term k) : Program k :=
 applyTwo HistoryCodec.pair (constant k 0)
  (applyTwo HistoryCodec.pair (LiteralEqualityQuote.equalityQuote t t)
   (applyTwo HistoryCodec.pair (constant k 0)
    (applyTwo HistoryCodec.pair (constant k 11)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons (LiteralTemplateQuote.templateQuote t) (constant k 0))
      (applyTwo HistoryCodec.pair (constant k 0) (constant k 0))))))
def lineValue {ctx : Nat} (ptag ctag : Nat) (rawEquality rawTerm : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag rawEquality
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (Term.numeral 11)
     (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag rawTerm .zero)
      (HistoryKernel.pairCall ptag .zero .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote
