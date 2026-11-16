module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.GraphSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.LineGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof GraphSupport
theorem lineAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag atag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (isExists : Bool) (f g : Program arity) (values : List.Vector (Term ctx) arity) (a b : Term ctx)
 (hf : Computes p G f values a) (hg : Computes p G g values b) :
 Computes p G (line isExists f g) values (lineValue isExists ptag ctag atag a b) := by
 have hz := constantValue p G values 0
 have htag := constantValue p G values (if isExists then 10 else 2)
 have hconclusion := conclusionAt p G ctag atag hc ha isExists f g values a b hf hg
 have hargs := argumentsAt p G ctag hc isExists f g values a b hf hg
 have hrefs := binary p G values HistoryCodec.pair _ _ _ _ _ hz hz (copies p G _ ptag hp _)
 have hpayload := binary p G values HistoryCodec.pair _ _ _ _ _ hargs hrefs (copies p G _ ptag hp _)
 have hannot := binary p G values HistoryCodec.pair _ _ _ _ _ htag hpayload (copies p G _ ptag hp _)
 have hrule := binary p G values HistoryCodec.pair _ _ _ _ _ hz hannot (copies p G _ ptag hp _)
 have hbody := binary p G values HistoryCodec.pair _ _ _ _ _ hconclusion hrule (copies p G _ ptag hp _)
 exact binary p G values HistoryCodec.pair _ _ _ _ _ hz hbody (copies p G _ ptag hp _)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.LineGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.LineGraph
