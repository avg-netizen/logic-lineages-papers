module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ContinuationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

theorem internalContinuation : Targets.InternalContinuation := by
 intro k t u n p qtag stag ptag ctag atag hq hs hp hc ha ctx values binder rest suffix
 obtain ⟨hscan⟩ := ScanProof.internalScan k t u n p qtag stag ptag ctag atag hq hs hp hc ha ctx values binder rest
 obtain ⟨hf⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx
  (HistoryLookup.consCall ctag (formulaTask ptag binder) rest)
  (quoteCall qtag values) suffix rest
 exact ⟨.mp hf hscan⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ContinuationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ContinuationProof
