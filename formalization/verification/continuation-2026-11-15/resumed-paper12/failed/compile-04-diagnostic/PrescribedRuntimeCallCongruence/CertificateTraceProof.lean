module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ScalarTraceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleStructureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.CertificateTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open GorbowClosedEquality GorbowRegistryTuple PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114

theorem mapHead {α β : Type} {n : Nat} (f : α → β) (v : List.Vector α (n+1)) :
 (v.map f).head = f v.head := by
 rw [← List.Vector.cons_head_tail v]
 rfl

theorem mapTail {α β : Type} {n : Nat} (f : α → β) (v : List.Vector α (n+1)) :
 (v.map f).tail = v.tail.map f := by
 rw [← List.Vector.cons_head_tail v]
 rfl

/-- Literal tail recursion, including the internally generated zero-arity proof. -/
set_option pp.all true in
theorem tuple {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩) :
 ∀ n (args others : List.Vector (Term 0) n) (codes : List.Vector Nat n),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (tupleCertificate J (args.map (rawNumeral (ctx := ctx)))
   (others.map rawNumeral) (codes.map Term.numeral)) (Term.numeral (tupleNumber args others codes)))) := by
 intro n
 induction n with
 | zero =>
  intro args others codes
  exact TraceCoreProof.reflexive p J hrc hrq zeroValue .zero (.logical (.reflexive _))
 | succ n ih =>
  intro args others codes
  obtain ⟨ht⟩ := ih args.tail others.tail codes.tail
  obtain ⟨hva⟩ := ValueTraceProof.tuple (ctx := ctx) p J hc hap args.tail.toList
  obtain ⟨hvb⟩ := ValueTraceProof.tuple (ctx := ctx) p J hc hap others.tail.toList
  obtain ⟨hp⟩ := ScalarTraceProof.pair p J hc hap hm hq hrc hrq
   (rawNumeral args.head) _ (rawNumeral others.head) _ (Term.numeral codes.head) _
   args.head (tupleTerm args.tail.toList) others.head (tupleTerm others.tail.toList)
   codes.head (tupleNumber args.tail others.tail codes.tail)
   (.logical (.reflexive _)) hva (.logical (.reflexive _)) hvb (.logical (.reflexive _)) ht
  obtain ⟨hvpa⟩ := ValueTraceProof.pair p J hc hap _ _ args.head (tupleTerm args.tail.toList)
   (.logical (.reflexive _)) hva
  obtain ⟨hvpb⟩ := ValueTraceProof.pair p J hc hap _ _ others.head (tupleTerm others.tail.toList)
   (.logical (.reflexive _)) hvb
  have hs := ScalarTraceProof.unary p J hc hap hm hq hrc hrq false _ _ _
   (pairTerm args.head (tupleTerm args.tail.toList)) (pairTerm others.head (tupleTerm others.tail.toList))
   _ hvpa hvpb hp
  simpa only [tupleCertificate,tupleNumber,mapHead,mapTail,List.Vector.toList_map,
   Bool.false_eq_true,if_false] using hs

/-- The original tag reflexivity, arity reflexivity and final U congruence occur
 in their fixed order; all supplied certificate numbers remain unrestricted. -/
theorem call {arity ctx n : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hap : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (tag : Nat) (args others : List.Vector (Term 0) n) (codes : List.Vector Nat n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callCertificate J (Term.numeral tag) (args.map (rawNumeral (ctx := ctx)))
   (others.map rawNumeral) (codes.map Term.numeral)) (Term.numeral (callNumber tag args others codes)))) := by
 let a := args.map (rawNumeral (ctx := ctx))
 let b := others.map (rawNumeral (ctx := ctx))
 let h := codes.map (Term.numeral (n := ctx))
 let tagRaw := LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral (n := ctx) tag)
 let arityRaw : Term ctx := rawNumeral (Term.numeral n)
 obtain ⟨ht⟩ := tuple (ctx := ctx) p J hc hap hm hq hrc hrq n args others codes
 obtain ⟨hva⟩ := ValueTraceProof.tuple (ctx := ctx) p J hc hap args.toList
 obtain ⟨hvb⟩ := ValueTraceProof.tuple (ctx := ctx) p J hc hap others.toList
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
 obtain ⟨hvha⟩ := ValueTraceProof.header (ctx := ctx) p J hc hap hn tag args
 obtain ⟨hvhb⟩ := ValueTraceProof.header (ctx := ctx) p J hc hap hn tag others
 exact ScalarTraceProof.unary p J hc hap hm hq hrc hrq true _ _ _
  (headerTerm n tag args.toList) (headerTerm n tag others.toList) _ hvha hvhb hh

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.CertificateTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.CertificateTraceProof
