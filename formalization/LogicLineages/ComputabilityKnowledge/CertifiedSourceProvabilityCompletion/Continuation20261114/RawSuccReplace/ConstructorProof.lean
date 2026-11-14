module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem computesLine {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (ptag ctag atag : Nat) (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (args : List.Vector (Term ctx) arity) (a b : Program arity) (av bv : Term ctx)
 (hA : Computes p G a args av) (hB : Computes p G b args bv) :
 Computes p G (line a b) args (lineValue ptag ctag atag av bv) := by
 have hz := constantValue p G args 0
 have htwo := constantValue p G args 2
 have htwelve := constantValue p G args 12
 have hcons (x y : Term ctx) := copies p G HistoryCodec.cons ctag hc (x ::ᵥ y ::ᵥ nil)
 have hpair (x y : Term ctx) := copies p G HistoryCodec.pair ptag hp (x ::ᵥ y ::ᵥ nil)
 have hbin (k : Nat) (a b : Program arity) (av bv : Term ctx)
   (hA : Computes p G a args av) (hB : Computes p G b args bv) :
   Computes p G (binaryRaw k a b) args (binaryValue ctag atag k av bv) := by
  have happ := binary p G args HistoryAppend.append a b av bv _ hA hB
   (copies p G HistoryAppend.append atag ha (av ::ᵥ bv ::ᵥ nil))
  exact binary p G args HistoryCodec.cons _ _ _ _ _ (constantValue p G args k) happ (hcons _ _)
 have hsa : Computes p G (RawAddSucc.successorRaw a) args (succValue ctag av) :=
  binary p G args HistoryCodec.cons _ _ _ _ _ htwo hA (hcons _ _)
 have hsb : Computes p G (RawAddSucc.successorRaw b) args (succValue ctag bv) :=
  binary p G args HistoryCodec.cons _ _ _ _ _ htwo hB (hcons _ _)
 have hvarTail := binary p G args HistoryCodec.cons _ _ _ _ _ hz hz (hcons _ _)
 have hvar := binary p G args HistoryCodec.cons _ _ _ _ _ hz hvarTail (hcons _ _)
 have hsvar := binary p G args HistoryCodec.cons _ _ _ _ _ htwo hvar (hcons _ _)
 have htemplate : Computes p G (templateRaw a) args (templateValue ctag atag av) := hbin 0 _ _ _ _ hsa hsvar
 have heq := hbin 0 _ _ _ _ hA hB
 have hself := hbin 0 _ _ _ _ hsa hsa
 have hcong := hbin 0 _ _ _ _ hsa hsb
 have himp := hbin 7 _ _ _ _ hself hcong
 have hformula : Computes p G (formulaRaw a b) args (formulaValue ctag atag av bv) := hbin 7 _ _ _ _ heq himp
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
 intro n p qtag ptag ctag atag hq hp hc ha ctx raw rawB
 obtain ⟨h⟩ := computesLine p [] ptag ctag atag hp hc ha (raw ::ᵥ rawB ::ᵥ nil)
  (.projection 0) (.projection 1) raw rawB (projection p [] _ 0) (projection p [] _ 1) qtag hq
 exact ⟨Hilbert.Local.finish h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.ConstructorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.ConstructorProof.internalLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.ConstructorProof.computesLine
