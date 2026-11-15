module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
/-- Generic literal builder computation, retaining original runtime input terms
and exact original tuple fields. No validation or source image premise. -/
theorem lineAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (caseTag predTag ptag ctag : Nat)
 (hcase : (nodes p)[caseTag]? = some ⟨1,UniformClosedCase12.caseCode⟩)
 (hpred : (nodes p)[predTag]? = some ⟨1,HistoryCodec.predecessor⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (f t u : Program arity) (values : List.Vector (Term ctx) arity) (formula left right : Term ctx)
 (hf : Computes p G f values formula) (ht : Computes p G t values left) (hu : Computes p G u values right) :
 Computes p G (line f t u) values (lineValue caseTag predTag ptag ctag formula left right) := by
 have hz := constantValue p G values 0
 have h12 := constantValue p G values 12
 have hthird := binary p G values HistoryCodec.cons _ _ _ _ _ hu hz (copies p G _ ctag hc _)
 have hlast := binary p G values HistoryCodec.cons _ _ _ _ _ ht hthird (copies p G _ ctag hc _)
 have hargs := binary p G values HistoryCodec.cons _ _ _ _ _ hf hlast (copies p G _ ctag hc _)
 have hcompiled := unary p G values UniformClosedCase12.caseCode _ _ _ hargs (copies p G _ caseTag hcase _)
 have hconclusion := unary p G values HistoryCodec.predecessor _ _ _ hcompiled (copies p G _ predTag hpred _)
 have hrefs := binary p G values HistoryCodec.pair _ _ _ _ _ hz hz (copies p G _ ptag hp _)
 have hpayload := binary p G values HistoryCodec.pair _ _ _ _ _ hargs hrefs (copies p G _ ptag hp _)
 have htag := binary p G values HistoryCodec.pair _ _ _ _ _ h12 hpayload (copies p G _ ptag hp _)
 have hrule := binary p G values HistoryCodec.pair _ _ _ _ _ hz htag (copies p G _ ptag hp _)
 have hbody := binary p G values HistoryCodec.pair _ _ _ _ _ hconclusion hrule (copies p G _ ptag hp _)
 exact binary p G values HistoryCodec.pair _ _ _ _ _ hz hbody (copies p G _ ptag hp _)
theorem exactInternalLine : Targets.InternalLine := by
 intro n p qtag caseTag predTag ptag ctag hq hcase hpred hp hc ctx formula left right
 obtain ⟨h⟩ := lineAt p [] caseTag predTag ptag ctag hcase hpred hp hc
  (.projection 0) (.projection 1) (.projection 2) (formula ::ᵥ left ::ᵥ right ::ᵥ nil) formula left right
  (projection p [] _ 0) (projection p [] _ 1) (projection p [] _ 2) qtag hq
 exact ⟨h.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.ConstructorProof
