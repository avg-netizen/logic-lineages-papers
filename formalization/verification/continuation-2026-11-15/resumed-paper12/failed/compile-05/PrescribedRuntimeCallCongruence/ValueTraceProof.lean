module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValueTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open GorbowRegistryTuple PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114

/-- The syntax constructors encode the literal arithmetic term at any depth. -/
theorem binary {arity ctx depth : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (multiply : Bool) (a b : Term ctx) (t u : Term depth)
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal a (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode t)))))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal b (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode u))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryValue J multiply a b)
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (binaryTerm multiply t u)))))) := by
 cases multiply
 · exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.binary
    p J.ctag J.atag hc ha 3 a b (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) ht hu
 · exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.binary
    p J.ctag J.atag hc ha 4 a b (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) ht hu

theorem pair {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (a b : Term ctx) (t u : Term 0)
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (rawNumeral t)))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (rawNumeral u))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (pairValue J a b) (rawNumeral (pairTerm t u)))) := by
 obtain ⟨hs⟩ := binary p J hc ha false a b t u ht hu
 obtain ⟨hm⟩ := binary p J hc ha true _ _ (.add t u) (.add t u) hs hs
 exact binary p J hc ha false _ a (.mul (.add t u) (.add t u)) t hm ht

theorem tuple {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (args : List (Term 0)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (tupleValue J (args.map (rawNumeral (ctx := ctx)))) (rawNumeral (tupleTerm args)))) := by
 induction args with
 | nil => exact ⟨.logical (.reflexive _)⟩
 | cons t ts ih =>
  obtain ⟨ht⟩ := ih
  obtain ⟨hp⟩ := pair p J hc ha (rawNumeral t) _ t (tupleTerm ts) (.logical (.reflexive _)) ht
  exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.unary p J.ctag hc 2 _
   (GorbowTermPrefixCode.encode (pairTerm t (tupleTerm ts))) hp

theorem numeral {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩) (value : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral (n := ctx) value))
   (rawNumeral (Term.numeral value)))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p J.numeralTag
  LiteralNumeralPrefix.numeralCode hn (value ::ᵥ nil) ctx
 rw [LiteralNumeralPrefix.StatementChecks.exactNative] at h
 simpa only [rawNumeral,LiteralNumeralPrefix.numeralCall,List.Vector.map_cons,List.Vector.map_nil] using
  (show Nonempty _ from ⟨h⟩)

theorem header {arity ctx n : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (tag : Nat) (args : List.Vector (Term 0) n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (headerValue J (Term.numeral tag) (args.map (rawNumeral (ctx := ctx))))
   (rawNumeral (headerTerm n tag args.toList)))) := by
 obtain ⟨ht⟩ := tuple (ctx := ctx) p J hc ha args.toList
 obtain ⟨hnumeral⟩ := numeral (ctx := ctx) p J hn tag
 obtain ⟨hp⟩ := pair p J hc ha _ _ (Term.numeral tag) (tupleTerm args.toList) hnumeral ht
 exact pair p J hc ha _ _ (Term.numeral n) (pairTerm (Term.numeral tag) (tupleTerm args.toList))
  (.logical (.reflexive _)) hp

theorem call {arity ctx n : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (tag : Nat) (args : List.Vector (Term 0) n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callValue J (Term.numeral tag) (args.map (rawNumeral (ctx := ctx))))
   (rawNumeral (GorbowPRDefiningEquations.call tag args)))) := by
 obtain ⟨hh⟩ := header (ctx := ctx) p J hc ha hn tag args
 exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.unary p J.ctag hc 5 _
  (GorbowTermPrefixCode.encode (headerTerm n tag args.toList)) hh

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValueTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValueTraceProof
