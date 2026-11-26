module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TraceOperations
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnaryTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem trace {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (tTemplate : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs tTemplate old a x) (f : Term 1) (t u : Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (unaryRuleCertificate I boundEnvironment f nil (rawNumeral (ctx := ctx) t) (rawNumeral u))
   (Term.numeral (unaryRuleNumber f t u)))) := by
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 have hc := I.previous.current.h_ctag
 have ha := I.previous.current.h_atag
 have hq := I.previous.current.h_constructor
 let T := GorbowPRNumeralCalculation.Theory p
 let ft := specializedValue J.ctag J.atag boundEnvironment f (nil : List.Vector (Term ctx) 0) (rawNumeral t)
 let fu := specializedValue J.ctag J.atag boundEnvironment f (nil : List.Vector (Term ctx) 0) (rawNumeral u)
 let F := FixedFormulaSubstitution.termValue J.ctag J.atag boundEnvironment (nil : List.Vector (Term ctx) 0) f
 let matrix := equalValue J.ctag J.atag ft F
 let rr := equalValue J.ctag J.atag ft ft
 let out := equalValue J.ctag J.atag ft fu
 let nt := GorbowClosedEquality.instantiateTerm f t
 let nu := GorbowClosedEquality.instantiateTerm f u
 obtain ⟨hft⟩ := EncodingProof.specialized (ctx := ctx) p J.ctag J.atag hc ha f t
 obtain ⟨hfu⟩ := EncodingProof.specialized (ctx := ctx) p J.ctag J.atag hc ha f u
 obtain ⟨hf⟩ := EncodingProof.bound (ctx := ctx) p J.ctag J.atag hc ha f
 have hftLift : Derivation T (.equal ft
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm 1 nt))))) := by
  rw [EncodingProof.liftEncode]
  exact hft
 obtain ⟨hmat⟩ := EncodingProof.equal p J.ctag J.atag hc ha ft F (GorbowClosedEquality.liftClosedTerm 1 nt) f hftLift hf
 obtain ⟨hseed⟩ := TraceGraphProof.replacement p J.ctag J.constructorTag hc hq matrix
  (.equal (GorbowClosedEquality.liftClosedTerm 1 nt) f) t u hmat
 obtain ⟨hrr⟩ := EncodingProof.equal p J.ctag J.atag hc ha ft ft nt nt hft hft
 obtain ⟨houtEq⟩ := EncodingProof.equal p J.ctag J.atag hc ha ft fu nt nu hft hfu
 obtain ⟨hP⟩ := EncodingProof.equal (ctx := ctx) p J.ctag J.atag hc ha (rawNumeral t) (rawNumeral u) t u
  (.logical (.reflexive _)) (.logical (.reflexive _))
 obtain ⟨href⟩ := TraceGraphProof.reflexive p J.rctag J.reflexivityTag
  I.previous.previous.previous.previous.previous.hc I.previous.previous.previous.previous.previous.hreflexivity ft nt hft
 obtain ⟨hlift⟩ := TraceOperations.lift p installed lhs rhs tTemplate old a x I rr
  (equalValue J.ctag J.atag (rawNumeral t) (rawNumeral u))
  (RawCumulativeLogical.certificate J.rctag J.reflexivityTag ft) (.equal nt nt) (.equal t u) _ hrr hP href
 exact TraceOperations.mpUnder p installed lhs rhs tTemplate old a x I
  (equalValue J.ctag J.atag (rawNumeral t) (rawNumeral u)) rr out _ _
  (.equal t u) (.equal nt nt) (.equal nt nu) _ _ hP hrr houtEq hseed hlift
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnaryTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnaryTraceProof
