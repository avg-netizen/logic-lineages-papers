module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TermCopiesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CallEncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence GorbowRegistryTuple
theorem numeral {arity n depth inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (value : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag e raw (Term.numeral value)) (rawNumeral (Term.numeral value)))) := by
 induction value with
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ v ih =>
  obtain ⟨ih⟩ := ih
  exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.unary p ctag hc 2 _
   (GorbowTermPrefixCode.encode (Term.numeral (n := 0) v)) ih
theorem pairMap {n depth inputs ctx : Nat} (J : PrescribedRuntimeCallCongruence.Tags)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (a b : Term n) :
 termValue J.ctag J.atag e raw (pairTerm a b) =
 pairValue J (termValue J.ctag J.atag e raw a) (termValue J.ctag J.atag e raw b) := rfl
theorem tupleMap {n depth inputs ctx : Nat} (J : PrescribedRuntimeCallCongruence.Tags)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (args : List (Term n)) :
 termValue J.ctag J.atag e raw (tupleTerm args) =
 tupleValue J (args.map (termValue J.ctag J.atag e raw)) := by
 induction args with
 | nil => rfl
 | cons a as ih =>
  simp only [tupleTerm,termValue,pairMap,List.map_cons,tupleValue,ih]
theorem pairCongruence {arity ctx : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (a a' b b' : Term ctx)
 (haa : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a a'))
 (hbb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b b')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (pairValue J a b) (pairValue J a' b'))) := by
 obtain ⟨hs⟩ := CodecProof.binary p J.ctag J.atag J.ctag J.atag 3 hc ha hc ha _ _ _ _ haa hbb
 obtain ⟨hm⟩ := CodecProof.binary p J.ctag J.atag J.ctag J.atag 4 hc ha hc ha _ _ _ _ hs hs
 exact CodecProof.binary p J.ctag J.atag J.ctag J.atag 3 hc ha hc ha _ _ _ _ hm haa
theorem call {arity n depth inputs ctx m : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (tag : Nat)
 (args : List.Vector (Term n) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag e raw (GorbowPRDefiningEquations.call tag args))
   (callValue J (Term.numeral tag) (args.map (termValue J.ctag J.atag e raw))))) := by
 obtain ⟨hArity⟩ := numeral p J.ctag J.atag hc e raw m
 obtain ⟨hTag⟩ := numeral p J.ctag J.atag hc e raw tag
 obtain ⟨hNum⟩ := ValueTraceProof.numeral (ctx := ctx) p J hn tag
 have hTag' := Logic.trans _ _ _ hTag (Support.equalitySymmetry _ _ hNum)
 obtain ⟨hp⟩ := pairCongruence p J hc ha _ _ _ _ hTag'
  (.logical (.reflexive (tupleValue J (args.toList.map (termValue J.ctag J.atag e raw)))))
 obtain ⟨hh⟩ := pairCongruence p J hc ha _ _ _ _ hArity hp
 obtain ⟨hu⟩ := CodecProof.unary p J.ctag J.ctag 5 hc hc _ _ hh
 simpa only [GorbowPRDefiningEquations.call,headerTerm,termValue,pairMap,tupleMap,
  callValue,headerValue,List.Vector.toList_map] using (show Nonempty _ from ⟨hu⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CallEncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CallEncodingProof
