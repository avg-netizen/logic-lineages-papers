module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceTupleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceCallProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality GorbowRegistryTuple
theorem call {arity ctx n : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (tag : Nat) (a b h : List.Vector (Term ctx) n)
 (args others : List.Vector (Term 0) n) (codes : List.Vector Nat n)
 (hA : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (rawNumeral (args.get i)))))
 (hB : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (b.get i) (rawNumeral (others.get i)))))
 (hH : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (h.get i) (Term.numeral (codes.get i))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callCertificate J (Term.numeral tag) a b h) (Term.numeral (callNumber tag args others codes)))) := by
 let tagRaw := LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral (n := ctx) tag)
 let arityRaw : Term ctx := rawNumeral (Term.numeral n)
 obtain ⟨ht⟩ := TraceTupleProof.tuple (ctx := ctx) p J hc hap hm hq hrc hrq n a b h args others codes hA hB hH
 obtain ⟨hva⟩ := TraceTupleProof.value p J hc hap a args hA
 obtain ⟨hvb⟩ := TraceTupleProof.value p J hc hap b others hB
 obtain ⟨hvtag⟩ := ValueTraceProof.numeral (ctx := ctx) p J hn tag
 obtain ⟨htag⟩ := TraceCoreProof.reflexive p J hrc hrq tagRaw (Term.numeral tag) hvtag
 obtain ⟨hnat⟩ := TraceCoreProof.reflexive p J hrc hrq arityRaw (Term.numeral n) (.logical (.reflexive _))
 obtain ⟨hp⟩ := ScalarTraceProof.pair p J hc hap hm hq hrc hrq
  tagRaw (tupleValue J a.toList) tagRaw (tupleValue J b.toList)
  (reflexivityCertificate J tagRaw) (tupleCertificate J a b h)
  (Term.numeral tag) (tupleTerm args.toList) (Term.numeral tag) (tupleTerm others.toList)
  (reflexivityNumber (Term.numeral tag)) (tupleNumber args others codes) hvtag hva hvtag hvb htag ht
 obtain ⟨hvpa⟩ := ValueTraceProof.pair p J hc hap tagRaw (tupleValue J a.toList)
  (Term.numeral tag) (tupleTerm args.toList) hvtag hva
 obtain ⟨hvpb⟩ := ValueTraceProof.pair p J hc hap tagRaw (tupleValue J b.toList)
  (Term.numeral tag) (tupleTerm others.toList) hvtag hvb
 obtain ⟨hh⟩ := ScalarTraceProof.pair p J hc hap hm hq hrc hrq
  arityRaw (pairValue J tagRaw (tupleValue J a.toList)) arityRaw (pairValue J tagRaw (tupleValue J b.toList))
  (reflexivityCertificate J arityRaw)
  (pairCertificate J tagRaw (tupleValue J a.toList) tagRaw (tupleValue J b.toList)
   (reflexivityCertificate J tagRaw) (tupleCertificate J a b h))
  (Term.numeral n) (pairTerm (Term.numeral tag) (tupleTerm args.toList))
  (Term.numeral n) (pairTerm (Term.numeral tag) (tupleTerm others.toList)) _ _
  (.logical (.reflexive _)) hvpa (.logical (.reflexive _)) hvpb hnat hp
 obtain ⟨hvha⟩ := ValueTraceProof.pair p J hc hap arityRaw _ (Term.numeral n)
  (pairTerm (Term.numeral tag) (tupleTerm args.toList)) (.logical (.reflexive _)) hvpa
 obtain ⟨hvhb⟩ := ValueTraceProof.pair p J hc hap arityRaw _ (Term.numeral n)
  (pairTerm (Term.numeral tag) (tupleTerm others.toList)) (.logical (.reflexive _)) hvpb
 exact ScalarTraceProof.unary p J hc hap hm hq hrc hrq true _ _ _
  (headerTerm n tag args.toList) (headerTerm n tag others.toList) _ hvha hvhb hh

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceCallProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceCallProof
