module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.ScanProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.ContinuationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

theorem internalContinuation : Targets.InternalContinuation := by
 intro n p ntag stag ptag ctag atag hn hs hp hc ha ctx value binder rest suffix
 obtain ⟨hscan⟩ := ScanProof.internalScan n p ntag stag ptag ctag hn hs hp hc ctx value binder rest
 obtain ⟨hf⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx
  (HistoryLookup.consCall ctag (termTask ptag binder) rest) (numeralCall ntag value) suffix rest
 exact ⟨.mp hf hscan⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.ContinuationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.ContinuationProof
