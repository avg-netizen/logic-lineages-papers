module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.PairProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ReflexivityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open PrescribedRuntimeEquality
theorem current {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (index fuel : Term ctx) :
 ∀ n (args others codes : List.Vector (Term ctx) n),
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (args.get i)))) →
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (others.get i)))) →
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag (args.get i) (others.get i)) (codes.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.current.coreTag I.current.verifierTag index fuel
   (equalValue I.current.ctag I.current.atag (tupleValue (tags I) args.toList) (tupleValue (tags I) others.toList))
   (tupleCertificate (tags I) args others codes))) := by
 intro n
 induction n with
 | zero =>
  intro args others codes ha hb hh
  obtain ⟨hz⟩ := ValidityProof.closed p _ _ _ I.current G (.zero : Term 0)
  have h := ReflexivityProof.current p f lhs rhs t old arithmetic x I G (zeroValue : Term ctx) index fuel hz
  simpa only [TupleStructureProof.zero,tupleCertificate] using h
 | succ n ih =>
  intro args others codes ha hb hh
  have hat : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.current.vtag (args.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using ha i.succ
  have hbt : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.current.vtag (others.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using hb i.succ
  have hht : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (core I.current.coreTag index fuel
    (equalValue I.current.ctag I.current.atag (args.tail.get i) (others.tail.get i)) (codes.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using hh i.succ
  obtain ⟨ht⟩ := ih args.tail others.tail codes.tail hat hbt hht
  have htc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ht
  obtain ⟨hva⟩ := TupleValidityProof.current p f lhs rhs t old arithmetic x I G n args.tail hat
  obtain ⟨hvb⟩ := TupleValidityProof.current p f lhs rhs t old arithmetic x I G n others.tail hbt
  have hah : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.current.vtag args.head)) := by
   simpa only [List.Vector.get_zero] using ha 0
  have hbh : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.current.vtag others.head)) := by
   simpa only [List.Vector.get_zero] using hb 0
  have hhh : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag args.head others.head) codes.head)) := by
   simpa only [List.Vector.get_zero] using hh 0
  obtain ⟨hah⟩ := hah
  obtain ⟨hbh⟩ := hbh
  obtain ⟨hhh⟩ := hhh
  obtain ⟨hp⟩ := PairProof.current p f lhs rhs t old arithmetic x I G
   args.head (tupleValue (tags I) args.tail.toList) others.head (tupleValue (tags I) others.tail.toList)
   codes.head (tupleCertificate (tags I) args.tail others.tail codes.tail) index fuel hah hva hbh hvb hhh htc
  have hpc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hp
  obtain ⟨hvpa⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I G _ _ hah hva
  obtain ⟨hvpb⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I G _ _ hbh hvb
  rw [TupleStructureProof.succ,TupleStructureProof.succ]
  exact ScalarProof.unary p f lhs rhs t old arithmetic x I G false _ _ _ index fuel hvpa hvpb hpc
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleProof
