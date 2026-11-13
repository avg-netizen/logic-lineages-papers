module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.LineTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.LineInternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open HistoryRuleSuffix LiteralRawMP.ConstructorSupportProof

theorem internalEquation : LineTargets.InternalEquation := by
 intro k t n p qtag etag ttag ptag ctag hq he ht hp hc ctx values
 have hterm : Computes p (LiteralTemplateQuote.templateQuote t) values (call ttag values) := by
  intro other ho
  exact GorbowPRInternalCoherence.Proof.registryCoherence n p other ttag k
   (LiteralTemplateQuote.templateQuote t) ho ht ctx values
 have hequal : Computes p (LiteralEqualityQuote.equalityQuote t t) values (call etag values) := by
  intro other ho
  exact GorbowPRInternalCoherence.Proof.registryCoherence n p other etag k
   (LiteralEqualityQuote.equalityQuote t t) ho he ctx values
 have hz := constantValue p values 0
 have htag := constantValue p values 11
 have hsingle := binary p values HistoryCodec.cons ctag hc _ _ _ _ hterm hz
 have hrefs := binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hz
 have hargs := binary p values HistoryCodec.pair ptag hp _ _ _ _ hsingle hrefs
 have hpayload := binary p values HistoryCodec.pair ptag hp _ _ _ _ htag hargs
 have hrule := binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hpayload
 have hconclusion := binary p values HistoryCodec.pair ptag hp _ _ _ _ hequal hrule
 exact binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hconclusion qtag hq
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.LineInternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.LineInternalProof
