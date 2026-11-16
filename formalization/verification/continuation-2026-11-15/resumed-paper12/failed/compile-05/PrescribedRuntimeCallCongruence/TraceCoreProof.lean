module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValueTraceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TraceCoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open GorbowClosedEquality PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114

/-- Subterms may be computed syntax values; the original singleton line and its
 two replacements remain literal. -/
theorem replacement {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (A a b : Term ctx) (f : Formula 1) (t u : Term 0)
 (hA : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal A (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag A a b)
   (Term.numeral (replacementNumber f t u)))) := by
 have hl := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) J.constructorTag
  (A ::ᵥ a ::ᵥ b ::ᵥ nil) (A ::ᵥ rawNumeral t ::ᵥ rawNumeral u ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact ha
     | succ i => cases i using Fin.cases with
       | zero => exact hb
       | succ i => exact Fin.elim0 i)
 have hs := HistoryAppend.PositiveProof.binaryCongruence J.ctag _ _ (.zero : Term ctx) .zero
  hl (.logical (.reflexive .zero))
 obtain ⟨hn⟩ := PrescribedRuntimeEquality.TraceGraphProof.replacement p J.ctag J.constructorTag hc hq A f t u hA
 exact ⟨Logic.trans _ _ _ hs hn⟩

theorem reflexive {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (a : Term ctx) (t : Term 0)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (reflexivityCertificate J a) (Term.numeral (reflexivityNumber t)))) := by
 exact PrescribedRuntimeEquality.TraceGraphProof.reflexive p J.rctag J.reflexivityTag hc hq a t ha

/-- Exact two-MP trace, including arbitrary native certificate numbers. -/
theorem transitivity {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (a b c hab hbc : Term ctx) (t u v : Term 0) (htu huv : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal c (rawNumeral v)))
 (hhab : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hab (Term.numeral htu)))
 (hhbc : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hbc (Term.numeral huv))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transitivityCertificate J.mtag J.ctag J.atag J.constructorTag a b c hab hbc)
   (Term.numeral (transitivityNumber t u v htu huv)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let matrix := equalValue J.ctag J.atag a
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
 let tu := equalValue J.ctag J.atag a b
 let tv := equalValue J.ctag J.atag a c
 have ht : Derivation T (.equal a
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (liftClosedTerm 1 t))))) := by
  rw [PrescribedRuntimeEquality.EncodingProof.liftEncode]
  exact ha
 obtain ⟨hmat⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc hap _ _
  (liftClosedTerm 1 t) (.var (0 : Fin 1)) ht (.logical (.reflexive _))
 obtain ⟨hseed⟩ := replacement p J hc hq matrix b c
  (.equal (liftClosedTerm 1 t) (.var 0)) u v hmat hb hv
 obtain ⟨htuEq⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc hap a b t u ha hb
 obtain ⟨htvEq⟩ := PrescribedRuntimeEquality.EncodingProof.equal p J.ctag J.atag hc hap a c t v ha hv
 obtain ⟨himp⟩ := PrescribedRuntimeEquality.EncodingProof.imp p J.ctag J.atag hc hap tu tv
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
