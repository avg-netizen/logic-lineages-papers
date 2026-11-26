module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem computesLine {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (ptag ctag atag : Nat) (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (args : List.Vector (Term ctx) arity) (a b v : Program arity) (av bv vv : Term ctx)
 (hA : Computes p G a args av) (hB : Computes p G b args bv) (hV : Computes p G v args vv) :
 Computes p G (line a b v) args (lineValue ptag ctag atag av bv vv) := by
 have hz := constantValue p G args 0
 have htwo := constantValue p G args 2
 have htwelve := constantValue p G args 12
 have hcons (x y : Term ctx) := copies p G HistoryCodec.cons ctag hc (x ::ᵥ y ::ᵥ nil)
 have hpair (x y : Term ctx) := copies p G HistoryCodec.pair ptag hp (x ::ᵥ y ::ᵥ nil)
 have hbin (k : Nat) (a b : Program arity) (av bv : Term ctx)
   (hA : Computes p G a args av) (hB : Computes p G b args bv) :
   Computes p G (RawSuccReplace.binaryRaw k a b) args (binaryValue ctag atag k av bv) := by
  have happ := binary p G args HistoryAppend.append a b av bv _ hA hB
   (copies p G HistoryAppend.append atag ha (av ::ᵥ bv ::ᵥ nil))
  exact binary p G args HistoryCodec.cons _ _ _ _ _ (constantValue p G args k) happ (hcons _ _)
 have hv0 := binary p G args HistoryCodec.cons _ _ _ _ _ hz hz (hcons _ _)
 have hvar := binary p G args HistoryCodec.cons _ _ _ _ _ hz hv0 (hcons _ _)
 have hav := hbin 3 _ _ _ _ hV hA
 have hbv := hbin 3 _ _ _ _ hV hB
 have hxv := hbin 3 _ _ _ _ hV hvar
 have htemplate : Computes p G (templateRaw a v) args (templateValue ctag atag av vv) := hbin 0 _ _ _ _ hav hxv
 have heq := hbin 0 _ _ _ _ hA hB
 have hself := hbin 0 _ _ _ _ hav hav
 have hcong := hbin 0 _ _ _ _ hav hbv
 have himp := hbin 7 _ _ _ _ hself hcong
 have hformula : Computes p G (formulaRaw a b v) args (formulaValue ctag atag av bv vv) := hbin 7 _ _ _ _ heq himp
 have hlast := binary p G args HistoryCodec.cons _ _ _ _ _ hB hz (hcons _ _)
 have hargs2 := binary p G args HistoryCodec.cons _ _ _ _ _ hA hlast (hcons _ _)
 have hargs3 := binary p G args HistoryCodec.cons _ _ _ _ _ htemplate hargs2 (hcons _ _)
 have hrefs := binary p G args HistoryCodec.pair _ _ _ _ _ hz hz (hpair _ _)
 have hargs := binary p G args HistoryCodec.pair _ _ _ _ _ hargs3 hrefs (hpair _ _)
 have hpay := binary p G args HistoryCodec.pair _ _ _ _ _ htwelve hargs (hpair _ _)
 have hrule := binary p G args HistoryCodec.pair _ _ _ _ _ hz hpay (hpair _ _)
 have hconcl := binary p G args HistoryCodec.pair _ _ _ _ _ hformula hrule (hpair _ _)
 exact binary p G args HistoryCodec.pair _ _ _ _ _ hz hconcl (hpair _ _)

theorem internalLine : Targets.InternalLine := by
 intro n p qtag ptag ctag atag hq hp hc ha ctx raw rawB rawV
 obtain ⟨h⟩ := computesLine p [] ptag ctag atag hp hc ha (raw ::ᵥ rawB ::ᵥ rawV ::ᵥ nil)
  (.projection 0) (.projection 1) (.projection 2) raw rawB rawV (projection p [] _ 0) (projection p [] _ 1) (projection p [] _ 2) qtag hq
 exact ⟨Hilbert.Local.finish h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.ConstructorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.ConstructorProof.internalLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.ConstructorProof.computesLine
