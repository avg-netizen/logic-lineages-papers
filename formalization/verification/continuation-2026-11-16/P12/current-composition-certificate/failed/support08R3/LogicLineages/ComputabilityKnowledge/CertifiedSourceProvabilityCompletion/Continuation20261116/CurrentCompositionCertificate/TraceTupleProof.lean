module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceTupleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality GorbowRegistryTuple
theorem value {arity ctx n : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (a : List.Vector (Term ctx) n) (args : List.Vector (Term 0) n)
 (h : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (rawNumeral (args.get i))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (tupleValue J a.toList) (rawNumeral (tupleTerm args.toList)))) := by
 have he : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (a.get i) ((args.map (rawNumeral (ctx := ctx))).get i))) := by
  intro i
  simpa only [List.Vector.get_map] using h i
 obtain ⟨hcng⟩ := ValueCongruenceProof.tuples p J hc ha n a (args.map rawNumeral) he
 obtain ⟨hn⟩ := ValueTraceProof.tuple (ctx := ctx) p J hc ha args.toList
 rw [List.Vector.toList_map] at hcng
 exact ⟨Logic.trans _ _ _ hcng hn⟩
theorem tuple {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hrq : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩) :
 ∀ n (a b h : List.Vector (Term ctx) n) (args others : List.Vector (Term 0) n) (codes : List.Vector Nat n),
 (∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (rawNumeral (args.get i))))) →
 (∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (b.get i) (rawNumeral (others.get i))))) →
 (∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (h.get i) (Term.numeral (codes.get i))))) →
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (tupleCertificate J a b h) (Term.numeral (tupleNumber args others codes)))) := by
 intro n
 induction n with
 | zero =>
  intro a b h args others codes hA hB hH
  exact TraceCoreProof.reflexive p J hrc hrq zeroValue .zero (.logical (.reflexive _))
 | succ n ih =>
  intro a b h args others codes hA hB hH
  obtain ⟨av,as,rfl⟩ := List.Vector.exists_eq_cons a
  obtain ⟨bv,bs,rfl⟩ := List.Vector.exists_eq_cons b
  obtain ⟨hv,hs,rfl⟩ := List.Vector.exists_eq_cons h
  obtain ⟨at,ats,rfl⟩ := List.Vector.exists_eq_cons args
  obtain ⟨bt,bts,rfl⟩ := List.Vector.exists_eq_cons others
  obtain ⟨hn,hns,rfl⟩ := List.Vector.exists_eq_cons codes
  have hAs : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (as.get i) (rawNumeral (ats.get i)))) := fun i => hA i.succ
  have hBs : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (bs.get i) (rawNumeral (bts.get i)))) := fun i => hB i.succ
  have hHs : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (hs.get i) (Term.numeral (hns.get i)))) := fun i => hH i.succ
  obtain ⟨hheadA⟩ := hA 0
  obtain ⟨hheadB⟩ := hB 0
  obtain ⟨hheadH⟩ := hH 0
  obtain ⟨ht⟩ := ih as bs hs ats bts hns hAs hBs hHs
  obtain ⟨hva⟩ := value p J hc ha as ats hAs
  obtain ⟨hvb⟩ := value p J hc ha bs bts hBs
  obtain ⟨hp⟩ := ScalarTraceProof.pair p J hc ha hm hq hrc hrq av _ bv _ hv _
   at (tupleTerm ats.toList) bt (tupleTerm bts.toList) hn (tupleNumber ats bts hns)
   hheadA hva hheadB hvb hheadH ht
  obtain ⟨hvpa⟩ := ValueTraceProof.pair p J hc ha _ _ at (tupleTerm ats.toList) hheadA hva
  obtain ⟨hvpb⟩ := ValueTraceProof.pair p J hc ha _ _ bt (tupleTerm bts.toList) hheadB hvb
  have hout := ScalarTraceProof.unary p J hc ha hm hq hrc hrq false _ _ _
   (pairTerm at (tupleTerm ats.toList)) (pairTerm bt (tupleTerm bts.toList)) _ hvpa hvpb hp
  set_option backward.isDefEq.respectTransparency false in
   simpa only [tupleCertificate,tupleNumber,List.Vector.head_cons,List.Vector.tail_cons,
    Bool.false_eq_true,if_false] using hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceTupleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceTupleProof
