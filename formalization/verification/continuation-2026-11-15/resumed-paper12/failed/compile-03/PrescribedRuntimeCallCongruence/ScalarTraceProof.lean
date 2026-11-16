module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TraceCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ScalarTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open GorbowClosedEquality GorbowRegistryTuple PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114

theorem instantiateLeft (multiply : Bool) (t u : Term 0) :
 instantiateTerm (binaryTerm multiply (.var 0) (liftClosedTerm 1 u)) t = binaryTerm multiply t u := by
 cases multiply
 · change Term.add t (GorbowSubstitution.substitute (Fin.cases t Fin.elim0) (liftClosedTerm 1 u)) = .add t u
   rw [GorbowClosedEqualityProof.closedTransport]
 · change Term.mul t (GorbowSubstitution.substitute (Fin.cases t Fin.elim0) (liftClosedTerm 1 u)) = .mul t u
   rw [GorbowClosedEqualityProof.closedTransport]

theorem instantiateRight (multiply : Bool) (t u : Term 0) :
 instantiateTerm (binaryTerm multiply (liftClosedTerm 1 t) (.var 0)) u = binaryTerm multiply t u := by
 cases multiply
 · change Term.add (GorbowSubstitution.substitute (Fin.cases u Fin.elim0) (liftClosedTerm 1 t)) u = .add t u
   rw [GorbowClosedEqualityProof.closedTransport]
 · change Term.mul (GorbowSubstitution.substitute (Fin.cases u Fin.elim0) (liftClosedTerm 1 t)) u = .mul t u
   rw [GorbowClosedEqualityProof.closedTransport]

theorem unary {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (universal : Bool) (a b code : Term ctx) (t u : Term 0) (htu : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (Term.numeral htu))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeCallCongruence.unaryCertificate J
   (if universal then .universalFunction (.var 0) else .succ (.var 0)) a b code)
   (Term.numeral (unaryNumber (if universal then .universalFunction (.var 0) else .succ (.var 0)) t u htu)))) := by
 let f : Term 1 := if universal then .universalFunction (.var 0) else .succ (.var 0)
 obtain ⟨hF⟩ := PrescribedRuntimeEquality.EncodingProof.bound (ctx := ctx) p J.ctag J.atag hc hap f
 obtain ⟨hft⟩ := FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.unary
  p J.ctag hc (if universal then 5 else 2) a (GorbowTermPrefixCode.encode t) ha
 obtain ⟨hfu⟩ := FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.unary
  p J.ctag hc (if universal then 5 else 2) b (GorbowTermPrefixCode.encode u) hb
 apply TraceCoreProof.unary p J hc hap hm hq hrc hrq boundEnvironment f nil a b code f t u htu ha hb hh hF
 · cases universal <;> exact hft
 · cases universal <;> exact hfu

/-- var1 denotes the original closed right coordinate, including its literal
 lifting under the protected var0. -/
theorem left {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (multiply : Bool) (a b c code : Term ctx) (t u v : Term 0) (htv : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal c (rawNumeral v)))
 (hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (Term.numeral htv))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag
   binaryEnvironment (binaryTerm multiply (.var 0) (.var 1)) (b ::ᵥ nil) a c code)
   (Term.numeral (unaryNumber (binaryTerm multiply (.var 0) (liftClosedTerm 1 u)) t v htv)))) := by
 have hbLift : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal b (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (liftClosedTerm 1 u))))) := by
  rw [PrescribedRuntimeEquality.EncodingProof.liftEncode]
  exact hb
 obtain ⟨hF⟩ := ValueTraceProof.binary p J hc hap multiply
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1))))) b
  (.var (0 : Fin 1)) (liftClosedTerm 1 u) (.logical (.reflexive _)) hbLift
 obtain ⟨hft⟩ := ValueTraceProof.binary p J hc hap multiply a b t u ha hb
 obtain ⟨hfu⟩ := ValueTraceProof.binary p J hc hap multiply c b v u hv hb
 apply TraceCoreProof.unary p J hc hap hm hq hrc hrq binaryEnvironment
  (binaryTerm multiply (.var 0) (.var 1)) (b ::ᵥ nil) a c code
  (binaryTerm multiply (.var 0) (liftClosedTerm 1 u)) t v htv ha hv hh
 · cases multiply <;> exact hF
 · rw [instantiateLeft]
   cases multiply <;> exact hft
 · rw [instantiateLeft]
   cases multiply <;> exact hfu

theorem right {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (multiply : Bool) (a b c code : Term ctx) (t u v : Term 0) (htv : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal c (rawNumeral v)))
 (hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (Term.numeral htv))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag
   binaryEnvironment (binaryTerm multiply (.var 1) (.var 0)) (b ::ᵥ nil) a c code)
   (Term.numeral (unaryNumber (binaryTerm multiply (liftClosedTerm 1 u) (.var 0)) t v htv)))) := by
 have hbLift : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal b (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (liftClosedTerm 1 u))))) := by
  rw [PrescribedRuntimeEquality.EncodingProof.liftEncode]
  exact hb
 obtain ⟨hF⟩ := ValueTraceProof.binary p J hc hap multiply b
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
  (liftClosedTerm 1 u) (.var (0 : Fin 1)) hbLift (.logical (.reflexive _))
 obtain ⟨hft⟩ := ValueTraceProof.binary p J hc hap multiply b a u t hb ha
 obtain ⟨hfu⟩ := ValueTraceProof.binary p J hc hap multiply b c u v hb hv
 apply TraceCoreProof.unary p J hc hap hm hq hrc hrq binaryEnvironment
  (binaryTerm multiply (.var 1) (.var 0)) (b ::ᵥ nil) a c code
  (binaryTerm multiply (liftClosedTerm 1 u) (.var 0)) t v htv ha hv hh
 · cases multiply <;> exact hF
 · rw [instantiateRight]
   cases multiply <;> exact hft
 · rw [instantiateRight]
   cases multiply <;> exact hfu

theorem binary {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (multiply : Bool) (a b c d hac hbd : Term ctx) (t u v w : Term 0) (htv huw : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal c (rawNumeral v)))
 (hw : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal d (rawNumeral w)))
 (hhac : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hac (Term.numeral htv)))
 (hhbd : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hbd (Term.numeral huw))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCertificate J multiply a b c d hac hbd) (Term.numeral (binaryNumber multiply t u v w htv huw)))) := by
 obtain ⟨hp⟩ := left p J hc hap hm hq hrc hrq multiply a b c hac t u v htv ha hb hv hhac
 obtain ⟨hq'⟩ := right p J hc hap hm hq hrc hrq multiply b c d hbd u v w huw hb hv hw hhbd
 obtain ⟨hab⟩ := ValueTraceProof.binary p J hc hap multiply a b t u ha hb
 obtain ⟨hcb⟩ := ValueTraceProof.binary p J hc hap multiply c b v u hv hb
 obtain ⟨hcd⟩ := ValueTraceProof.binary p J hc hap multiply c d v w hv hw
 exact TraceCoreProof.transitivity p J hc hap hm hq _ _ _ _ _
  (binaryTerm multiply t u) (binaryTerm multiply v u) (binaryTerm multiply v w) _ _ hab hcb hcd hp hq'

/-- The sum certificate is used twice by multiplication, then the original left
 input certificate is the second antecedent of the outer addition. -/
theorem pair {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (a b c d hac hbd : Term ctx) (t u v w : Term 0) (htv huw : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u)))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal c (rawNumeral v)))
 (hw : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal d (rawNumeral w)))
 (hhac : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hac (Term.numeral htv)))
 (hhbd : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hbd (Term.numeral huw))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (pairCertificate J a b c d hac hbd) (Term.numeral (pairNumber t u v w htv huw)))) := by
 obtain ⟨hs⟩ := binary p J hc hap hm hq hrc hrq false a b c d hac hbd t u v w htv huw ha hb hv hw hhac hhbd
 obtain ⟨hab⟩ := ValueTraceProof.binary p J hc hap false a b t u ha hb
 obtain ⟨hcd⟩ := ValueTraceProof.binary p J hc hap false c d v w hv hw
 obtain ⟨hmul⟩ := binary p J hc hap hm hq hrc hrq true _ _ _ _ _ _
  (.add t u) (.add t u) (.add v w) (.add v w) _ _ hab hab hcd hcd hs hs
 obtain ⟨hsqA⟩ := ValueTraceProof.binary p J hc hap true _ _ (.add t u) (.add t u) hab hab
 obtain ⟨hsqB⟩ := ValueTraceProof.binary p J hc hap true _ _ (.add v w) (.add v w) hcd hcd
 exact binary p J hc hap hm hq hrc hrq false _ a _ c _ hac
  (.mul (.add t u) (.add t u)) t (.mul (.add v w) (.add v w)) v _ htv
  hsqA ha hsqB hv hmul hhac

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ScalarTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ScalarTraceProof
