module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.InternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open HistoryRuleSuffix LiteralRawMP.ConstructorSupportProof

theorem internalEquation : Targets.InternalEquation := by
 intro k t n p qtag ttag ptag ctag hq ht hp hc ctx values
 have hterm : Computes p (LiteralTemplateQuote.templateQuote t) values (call ttag values) := by
  intro other ho
  exact GorbowPRInternalCoherence.Proof.registryCoherence n p other ttag k
   (LiteralTemplateQuote.templateQuote t) ho ht ctx values
 have hsingle := binary p values HistoryCodec.cons ctag hc
  (LiteralTemplateQuote.templateQuote t) (constant k 0) (call ttag values) .zero
  hterm (constantValue p values 0)
 exact binary p values HistoryCodec.pair ptag hp (constant k 11)
  (applyTwo HistoryCodec.cons (LiteralTemplateQuote.templateQuote t) (constant k 0))
  (Term.numeral 11) (HistoryLookup.consCall ctag (call ttag values) .zero)
  (constantValue p values 11) hsingle qtag hq
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.InternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.InternalProof
