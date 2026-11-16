module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.NativeLineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem binaryAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (values : List.Vector (Term ctx) arity) (f g : Program arity) (a b : Term ctx)
 (hf : Computes p G f values a) (hg : Computes p G g values b) :
 Computes p G (FixedFormulaSubstitution.binary 7 f g) values (PrescribedRuntimeEquality.impValue ctag atag a b) := by
 have happ := binary p G values HistoryAppend.append _ _ _ _ _ hf hg (copies p G _ atag ha _)
 exact binary p G values HistoryCodec.cons _ _ _ _ _ (constantValue p G values 7) happ (copies p G _ ctag hc _)
theorem conclusionAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (isS : Bool) (f g h : Program arity) (values : List.Vector (Term ctx) arity) (a b c : Term ctx)
 (hf : Computes p G f values a) (hg : Computes p G g values b) (hh : Computes p G h values c) :
 Computes p G (conclusion isS f g h) values (conclusionValue isS ctag atag a b c) := by
 cases isS with
 | false => exact binaryAt p G ctag atag hc ha values _ _ _ _ hf (binaryAt p G ctag atag hc ha values _ _ _ _ hg hf)
 | true =>
  exact binaryAt p G ctag atag hc ha values _ _ _ _
   (binaryAt p G ctag atag hc ha values _ _ _ _ hf (binaryAt p G ctag atag hc ha values _ _ _ _ hg hh))
   (binaryAt p G ctag atag hc ha values _ _ _ _
    (binaryAt p G ctag atag hc ha values _ _ _ _ hf hg)
    (binaryAt p G ctag atag hc ha values _ _ _ _ hf hh))
theorem argumentsAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (isS : Bool) (f g h : Program arity) (values : List.Vector (Term ctx) arity) (a b c : Term ctx)
 (hf : Computes p G f values a) (hg : Computes p G g values b) (hh : Computes p G h values c) :
 Computes p G (arguments isS f g h) values (argumentsValue isS ctag a b c) := by
 have hz := constantValue p G values 0
 have htail : Computes p G (if isS then applyTwo HistoryCodec.cons h (constant arity 0) else constant arity 0)
  values (if isS then HistoryLookup.consCall ctag c .zero else .zero) := by
  cases isS with
  | false => exact hz
  | true => exact binary p G values HistoryCodec.cons _ _ _ _ _ hh hz (copies p G _ ctag hc _)
 have hsecond := binary p G values HistoryCodec.cons _ _ _ _ _ hg htail (copies p G _ ctag hc _)
 exact binary p G values HistoryCodec.cons _ _ _ _ _ hf hsecond (copies p G _ ctag hc _)
theorem lineAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag atag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (isS : Bool) (f g h : Program arity) (values : List.Vector (Term ctx) arity) (a b c : Term ctx)
 (hf : Computes p G f values a) (hg : Computes p G g values b) (hh : Computes p G h values c) :
 Computes p G (line isS f g h) values (lineValue isS ptag ctag atag a b c) := by
 have hz := constantValue p G values 0
 have htag := constantValue p G values (if isS then 1 else 0)
 have hconclusion := conclusionAt p G ctag atag hc ha isS f g h values a b c hf hg hh
 have hargs := argumentsAt p G ctag hc isS f g h values a b c hf hg hh
 have hrefs := binary p G values HistoryCodec.pair _ _ _ _ _ hz hz (copies p G _ ptag hp _)
 have hpayload := binary p G values HistoryCodec.pair _ _ _ _ _ hargs hrefs (copies p G _ ptag hp _)
 have hannot := binary p G values HistoryCodec.pair _ _ _ _ _ htag hpayload (copies p G _ ptag hp _)
 have hrule := binary p G values HistoryCodec.pair _ _ _ _ _ hz hannot (copies p G _ ptag hp _)
 have hbody := binary p G values HistoryCodec.pair _ _ _ _ _ hconclusion hrule (copies p G _ ptag hp _)
 exact binary p G values HistoryCodec.pair _ _ _ _ _ hz hbody (copies p G _ ptag hp _)
theorem exactInternalLine : Targets.InternalLine := by
 intro n p isS qtag ptag ctag atag hq hp hc ha ctx a b c
 obtain ⟨h⟩ := lineAt p [] ptag ctag atag hp hc ha isS (.projection 0) (.projection 1) (.projection 2)
  (a ::ᵥ b ::ᵥ c ::ᵥ nil) a b c (projection p [] _ 0) (projection p [] _ 1) (projection p [] _ 2) qtag hq
 exact ⟨h.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.ConstructorProof
