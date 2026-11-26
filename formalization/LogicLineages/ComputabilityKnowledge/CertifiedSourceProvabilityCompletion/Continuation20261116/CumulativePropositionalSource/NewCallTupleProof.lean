module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.PairProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ReflexivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewTransitivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CallAlgebraTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallPairProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallReflexivityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallTupleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem current {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (index fuel : Term ctx) :
 ∀ n (args others codes : List.Vector (Term ctx) n),
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (args.get i)))) →
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (others.get i)))) →
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag (args.get i) (others.get i)) (codes.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue I.previous.current.ctag I.previous.current.atag (tupleValue (tags I.previous) args.toList) (tupleValue (tags I.previous) others.toList))
   (tupleCertificate (tags I.previous) args others codes))) := by
 intro n
 induction n with
 | zero =>
  intro args others codes ha hb hh
  obtain ⟨hz⟩ := ValidityProof.closed p _ _ _ I.previous.current G (.zero : Term 0)
  have h := NewCallReflexivityProof.current p f lhs rhs t old arithmetic x I G (zeroValue : Term ctx) index fuel hz
  simpa only [TupleStructureProof.zero,tupleCertificate] using h
 | succ n ih =>
  intro args others codes ha hb hh
  have hat : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.previous.current.vtag (args.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using ha i.succ
  have hbt : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.previous.current.vtag (others.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using hb i.succ
  have hht : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (core I.currentK.coreTag index fuel
    (equalValue I.previous.current.ctag I.previous.current.atag (args.tail.get i) (others.tail.get i)) (codes.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using hh i.succ
  obtain ⟨ht⟩ := ih args.tail others.tail codes.tail hat hbt hht
  have htc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ht
  obtain ⟨hva⟩ := TupleValidityProof.current p f lhs rhs t old arithmetic x I.previous G n args.tail hat
  obtain ⟨hvb⟩ := TupleValidityProof.current p f lhs rhs t old arithmetic x I.previous G n others.tail hbt
  have hah : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.previous.current.vtag args.head)) := by
   simpa only [List.Vector.get_zero] using ha 0
  have hbh : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.previous.current.vtag others.head)) := by
   simpa only [List.Vector.get_zero] using hb 0
  have hhh : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag args.head others.head) codes.head)) := by
   simpa only [List.Vector.get_zero] using hh 0
  obtain ⟨hah⟩ := hah
  obtain ⟨hbh⟩ := hbh
  obtain ⟨hhh⟩ := hhh
  obtain ⟨hp⟩ := NewCallPairProof.current p f lhs rhs t old arithmetic x I G
   args.head (tupleValue (tags I.previous) args.tail.toList) others.head (tupleValue (tags I.previous) others.tail.toList)
   codes.head (tupleCertificate (tags I.previous) args.tail others.tail codes.tail) index fuel hah hva hbh hvb hhh htc
  have hpc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hp
  obtain ⟨hvpa⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I.previous G _ _ hah hva
  obtain ⟨hvpb⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I.previous G _ _ hbh hvb
  rw [TupleStructureProof.succ,TupleStructureProof.succ]
  exact NewCallScalarProof.unary p f lhs rhs t old arithmetic x I G false _ _ _ index fuel hvpa hvpb hpc
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallTupleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallTupleProof
