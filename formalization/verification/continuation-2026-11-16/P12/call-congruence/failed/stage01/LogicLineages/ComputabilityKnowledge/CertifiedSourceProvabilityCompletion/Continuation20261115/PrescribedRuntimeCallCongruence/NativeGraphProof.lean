module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.NativeGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open PrescribedRuntimeEquality
theorem replacement {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (A left right : Term ctx) (f : Formula 1) (t u : Term 0)
 (hA : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal A (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal left (rawNumeral t)))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal right (rawNumeral u))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theor…12046 tokens truncated…eEquality.EncodingProof.imp p J.ctag J.atag hc hap tu tv
  (.equal t u) (.equal t v) htuEq htvEq
 obtain ⟨hfirst⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm
  (impValue J.ctag J.atag tu tv)
  (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix b c) hbc
  (.imp (.equal t u) (.equal t v)) (replacementNumber (.equal (liftClosedTerm 1 t) (.var 0)) u v) huv
  himp hseed hhbc
 obtain ⟨hout⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm tv
  (LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag tu tv)
   (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix b c) hbc)
  hab (.equal t v) _ htu htvEq hfirst hhab
 exact ⟨hout⟩

/-- A closed-coordinate environment is related to its exact instantiated open
 template by explicit prefix equations; no successful-certificate premise is used. -/
theorem unary {arity ctx n inputs : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (template : Term n)
 (raw : List.Vector (Term ctx) inputs) (a b hab : Term ctx) (f : Term 1) (t u : Term 0) (htu : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hhab : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hab (Term.numeral htu)))
 (hF : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (FixedFormulaSubstitution.termValue J.ctag J.atag e raw template)
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode f)))))
 (hft : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (specializedValue J.ctag J.atag e template raw a) (rawNumeral (instantiateTerm f t))))
 (hfu : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (specializedValue J.ctag J.atag e template raw b) (rawNumeral (instantiateTerm f u)))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag
   e template raw a b hab) (Term.numeral (unaryNumber f t u htu)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let ft := specializedValue J.ctag J.atag e template raw a
 let fu := specializedValue J.ctag J.atag e template raw b
 let F := FixedFormulaSubstitution.termValue J.ctag J.atag e raw template
 let matrix := equalValue J.ctag J.atag ft F
 let rr := equalValue J.ctag J.atag ft ft
 let out := equalValue J.ctag J.atag ft fu
 let nt := instantiateTerm f t
 let nu := instantiateTerm f u
 have hftLift : Derivation T (.equal ft
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (liftClosedTerm 1 nt))))) := by
  rw [PrescribedRuntimeEquality.EncodingProof.liftEncode]
  exact hft
 obtain ⟨hmat⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc hap ft F
  (liftClosedTerm 1 nt) f hftLift hF
 obtain ⟨hseed⟩ := replacement p J hc hq matrix a b (.equal (liftClosedTerm 1 nt) f) t u hmat ha hb
 obtain ⟨hrr⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc hap ft ft nt nt hft hft
 obtain ⟨houtEq⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc hap ft fu nt nu hft hfu
 obtain ⟨himp⟩ := PrescribedRuntimeEquality.EncodingProof.imp p J.ctag J.atag hc hap rr out
  (.equal nt nt) (.equal nt nu) hrr houtEq
 obtain ⟨hfirst⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm
  (impValue J.ctag J.atag rr out)
  (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix a b) hab
  (.imp (.equal nt nt) (.equal nt nu)) (replacementNumber (.equal (liftClosedTerm 1 nt) f) t u) htu
  himp hseed hhab
 obtain ⟨href⟩ := PrescribedRuntimeEquality.TraceGraphProof.reflexive p J.rctag J.reflexivityTag hrc hrq ft nt hft
 obtain ⟨hout⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm out
  (LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag rr out)
   (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix a b) hab)
  (RawCumulativeLogical.certificate J.rctag J.reflexivityTag ft) (.equal nt nu) _ _ houtEq hfirst href
 exact ⟨hout⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TraceCoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TraceCoreProof
