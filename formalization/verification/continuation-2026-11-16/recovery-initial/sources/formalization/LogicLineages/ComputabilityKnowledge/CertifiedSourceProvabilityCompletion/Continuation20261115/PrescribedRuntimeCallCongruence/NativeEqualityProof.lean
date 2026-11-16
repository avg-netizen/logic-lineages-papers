module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.NativeGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.NativeEqualityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open PrescribedRuntimeEquality
/-- Private graph refinement of the exact transitivity term for symbolic codes.
All graph hypotheses are proved by constructor arithmetic in the final trace. -/
theorem transitivity {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (a b c hfirst hsecond : Term ctx) (t u v : Term 0) (htu huv : Nat)
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal c (rawNumeral v)))
 (hhtu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hfirst (Term.numeral htu)))
 (hhuv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hsecond (Term.numeral huv))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transitivityCertificate J.mtag J.ctag J.atag J.constructorTag a b c hfirst hsecond)
   (Term.numeral (transitivityNumber t u v htu huv)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let matrix := equalValue J.ctag J.atag a
  (Term.numeral (n := ctx) (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
 let tu := equalValue J.ctag J.atag a b
 let tv := equalValue J.ctag J.atag a c
 have htLift : Derivation T (.equal a
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm 1 t))))) := by
  rw [PrescribedRuntimeEquality.EncodingProof.liftEncode]
  exact ht
 obtain ⟨hmat⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc ha _ _
  (GorbowClosedEquality.liftClosedTerm 1 t) (.var (0 : Fin 1)) htLift (.logical (.reflexive _))
 obtain ⟨hseed⟩ := NativeGraphProof.replacement p J hc hq matrix b c
  (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)) u v hmat hu hv
 obtain ⟨htuEq⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc ha a b t u ht hu
 obtain ⟨htvEq⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc ha a c t v ht hv
 obtain ⟨himp⟩ := PrescribedRuntimeEquality.EncodingProof.imp p J.ctag J.atag hc ha tu tv (.equal t u) (.equal t v) htuEq htvEq
 obtain ⟨h1⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm
  (impValue J.ctag J.atag tu tv) (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix b c)
  hsecond (.imp (.equal t u) (.equal t v))
  (replacementNumber (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)) u v) huv himp hseed hhuv
 obtain ⟨hout⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm tv
  (LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag tu tv)
   (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix b c) hsecond)
  hfirst (.equal t v) _ htu htvEq h1 hhtu
 exact ⟨hout⟩
/-- This proves the graph for the actual runtime-environment unary recipe.
Native f is only the trace comparator; it is not substituted for runtime syntax. -/
theorem unary {arity ctx n inputs : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (template : Term n)
 (raw : List.Vector (Term ctx) inputs) (a b code : Term ctx) (f : Term 1) (t u : Term 0) (htu : Nat)
 (hF : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (FixedFormulaSubstitution.termValue J.ctag J.atag e raw template)
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode f)))))
 (hft : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (specializedValue J.ctag J.atag e template raw a) (rawNumeral (GorbowClosedEquality.instantiateTerm f t))))
 (hfu : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (specializedValue J.ctag J.atag e template raw b) (rawNumeral (GorbowClosedEquality.instantiateTerm f u))))
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (Term.numeral htu))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag
   e template raw a b code) (Term.numeral (unaryNumber f t u htu)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let ft := specializedValue J.ctag J.atag e template raw a
 let fu := specializedValue J.ctag J.atag e template raw b
 let F := FixedFormulaSubstitution.termValue J.ctag J.atag e raw template
 let matrix := equalValue J.ctag J.atag ft F
 let rr := equalValue J.ctag J.atag ft ft
 let out := equalValue J.ctag J.atag ft fu
 let nt := GorbowClosedEquality.instantiateTerm f t
 let nu := GorbowClosedEquality.instantiateTerm f u
 have hftLift : Derivation T (.equal ft
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm 1 nt))))) := by
  rw [PrescribedRuntimeEquality.EncodingProof.liftEncode]
  exact hft
 obtain ⟨hmat⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc ha ft F
  (GorbowClosedEquality.liftClosedTerm 1 nt) f hftLift hF
 obtain ⟨hseed⟩ := NativeGraphProof.replacement p J hc hq matrix a b
  (.equal (GorbowClosedEquality.liftClosedTerm 1 nt) f) t u hmat ht hu
 obtain ⟨hrr⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc ha ft ft nt nt hft hft
 obtain ⟨houtEq⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc ha ft fu nt nu hft hfu
 obtain ⟨himp⟩ := PrescribedRuntimeEquality.EncodingProof.imp p J.ctag J.atag hc ha rr out (.equal nt nt) (.equal nt nu) hrr houtEq
 obtain ⟨hfirst⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm
  (impValue J.ctag J.atag rr out) (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix a b)
  code (.imp (.equal nt nt) (.equal nt nu))
  (replacementNumber (.equal (GorbowClosedEquality.liftClosedTerm 1 nt) f) t u) htu himp hseed hh
 obtain ⟨href⟩ := PrescribedRuntimeEquality.TraceGraphProof.reflexive p J.rctag J.reflexivityTag hrc hrq ft nt hft
 obtain ⟨hout⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm out
  (LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag rr out)
   (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix a b) code)
  (RawCumulativeLogical.certificate J.rctag J.reflexivityTag ft) (.equal nt nu) _ _ houtEq hfirst href
 exact ⟨hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.NativeEqualityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.NativeEqualityProof
