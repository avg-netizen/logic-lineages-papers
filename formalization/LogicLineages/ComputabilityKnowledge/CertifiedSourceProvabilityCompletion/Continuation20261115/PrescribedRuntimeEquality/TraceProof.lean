module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EncodingProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TraceGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem transitivity {arity ctx : Nat} (p : Program arity) (ctag atag mtag tag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[tag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (t u v : Term 0) (htu huv : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transitivityCertificate mtag ctag atag tag (rawNumeral (ctx := ctx) t)
   (rawNumeral u) (rawNumeral v) (Term.numeral htu) (Term.numeral huv))
   (Term.numeral (transitivityNumber t u v htu huv)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let matrix := equalValue ctag atag (rawNumeral (ctx := ctx) t)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
 let tu := equalValue ctag atag (rawNumeral (ctx := ctx) t) (rawNumeral u)
 let tv := equalValue ctag atag (rawNumeral (ctx := ctx) t) (rawNumeral v)
 have ht : Derivation T (.equal (rawNumeral (ctx := ctx) t)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm 1 t))))) := by
  rw [EncodingProof.liftEncode]
  exact .logical (.reflexive _)
 obtain ⟨hmat⟩ := EncodingProof.equal (ctx := ctx) p ctag atag hc ha _ _
  (GorbowClosedEquality.liftClosedTerm 1 t) (.var (0 : Fin 1)) ht (.logical (.reflexive _))
 obtain ⟨hseed⟩ := TraceGraphProof.replacement p ctag tag hc hq matrix
  (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)) u v hmat
 obtain ⟨htuEq⟩ := EncodingProof.equal (ctx := ctx) p ctag atag hc ha (rawNumeral t) (rawNumeral u) t u
  (.logical (.reflexive _)) (.logical (.reflexive _))
 obtain ⟨htvEq⟩ := EncodingProof.equal (ctx := ctx) p ctag atag hc ha (rawNumeral t) (rawNumeral v) t v
  (.logical (.reflexive _)) (.logical (.reflexive _))
 obtain ⟨himp⟩ := EncodingProof.imp p ctag atag hc ha tu tv (.equal t u) (.equal t v) htuEq htvEq
 obtain ⟨hfirst⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p mtag hm
  (impValue ctag atag tu tv)
  (UniformClosedRule12Certificate.certificate ctag tag matrix (rawNumeral u) (rawNumeral v))
  (Term.numeral huv) (.imp (.equal t u) (.equal t v))
  (replacementNumber (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)) u v) huv
  himp hseed (.logical (.reflexive _))
 obtain ⟨hout⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p mtag hm tv
  (LiteralMPRun.certificate mtag .zero (impValue ctag atag tu tv)
   (UniformClosedRule12Certificate.certificate ctag tag matrix (rawNumeral u) (rawNumeral v)) (Term.numeral huv))
  (Term.numeral htu) (.equal t v) _ htu htvEq hfirst (.logical (.reflexive _))
 exact ⟨hout⟩
theorem unary {arity ctx : Nat} (p : Program arity) (ctag atag mtag tag rctag reflexivityTag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[tag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (f : Term 1) (t u : Term 0) (htu : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (unaryCertificate mtag ctag atag tag rctag reflexivityTag boundEnvironment f nil
   (rawNumeral (ctx := ctx) t) (rawNumeral u) (Term.numeral htu))
   (Term.numeral (unaryNumber f t u htu)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let ft := specializedValue ctag atag boundEnvironment f (nil : List.Vector (Term ctx) 0) (rawNumeral t)
 let fu := specializedValue ctag atag boundEnvironment f (nil : List.Vector (Term ctx) 0) (rawNumeral u)
 let F := FixedFormulaSubstitution.termValue ctag atag boundEnvironment (nil : List.Vector (Term ctx) 0) f
 let matrix := equalValue ctag atag ft F
 let rr := equalValue ctag atag ft ft
 let out := equalValue ctag atag ft fu
 let nt := GorbowClosedEquality.instantiateTerm f t
 let nu := GorbowClosedEquality.instantiateTerm f u
 obtain ⟨hft⟩ := EncodingProof.specialized (ctx := ctx) p ctag atag hc ha f t
 obtain ⟨hfu⟩ := EncodingProof.specialized (ctx := ctx) p ctag atag hc ha f u
 obtain ⟨hf⟩ := EncodingProof.bound (ctx := ctx) p ctag atag hc ha f
 have hftLift : Derivation T (.equal ft
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm 1 nt))))) := by
  rw [EncodingProof.liftEncode]
  exact hft
 obtain ⟨hmat⟩ := EncodingProof.equal p ctag atag hc ha ft F (GorbowClosedEquality.liftClosedTerm 1 nt) f hftLift hf
 obtain ⟨hseed⟩ := TraceGraphProof.replacement p ctag tag hc hq matrix
  (.equal (GorbowClosedEquality.liftClosedTerm 1 nt) f) t u hmat
 obtain ⟨hrr⟩ := EncodingProof.equal p ctag atag hc ha ft ft nt nt hft hft
 obtain ⟨houtEq⟩ := EncodingProof.equal p ctag atag hc ha ft fu nt nu hft hfu
 obtain ⟨himp⟩ := EncodingProof.imp p ctag atag hc ha rr out (.equal nt nt) (.equal nt nu) hrr houtEq
 obtain ⟨hfirst⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p mtag hm
  (impValue ctag atag rr out)
  (UniformClosedRule12Certificate.certificate ctag tag matrix (rawNumeral t) (rawNumeral u))
  (Term.numeral htu) (.imp (.equal nt nt) (.equal nt nu))
  (replacementNumber (.equal (GorbowClosedEquality.liftClosedTerm 1 nt) f) t u) htu
  himp hseed (.logical (.reflexive _))
 obtain ⟨href⟩ := TraceGraphProof.reflexive p rctag reflexivityTag hrc hrq ft nt hft
 obtain ⟨hout⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p mtag hm out
  (LiteralMPRun.certificate mtag .zero (impValue ctag atag rr out)
   (UniformClosedRule12Certificate.certificate ctag tag matrix (rawNumeral t) (rawNumeral u)) (Term.numeral htu))
  (RawCumulativeLogical.certificate rctag reflexivityTag ft) (.equal nt nu) _ _ houtEq hfirst href
 exact ⟨hout⟩
theorem exactTraces : Targets.InternalPrescribedTraces := by
 intro arity k p installedFormula lhs rhs arithmeticTerm old arithmetic x I ctx t u v f htu huv
 obtain ⟨ht⟩ := transitivity (ctx := ctx) p I.current.ctag I.current.atag I.previous.previous.previous.previous.mpTag
  I.current.constructorTag I.current.h_ctag I.current.h_atag I.previous.previous.previous.previous.hmp
  I.current.h_constructor t u v htu huv
 obtain ⟨hu⟩ := unary (ctx := ctx) p I.current.ctag I.current.atag I.previous.previous.previous.previous.mpTag
  I.current.constructorTag I.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.reflexivityTag
  I.current.h_ctag I.current.h_atag I.previous.previous.previous.previous.hmp I.current.h_constructor
  I.previous.previous.previous.previous.hc I.previous.previous.previous.previous.hreflexivity f t u htu
 exact ⟨Derivation.mp (.mp (.logical (.andIntro _ _)) ht) hu⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TraceProof
