module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ConstructorValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleStructureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem current {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) : ∀ n (args : List.Vector (Term ctx) n),
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (args.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (tupleValue (tags I) args.toList))) := by
 intro n
 induction n with
 | zero =>
  intro args hargs
  rw [TupleStructureProof.zero]
  exact ValidityProof.closed p _ _ _ I.current G .zero
 | succ n ih =>
  intro args hargs
  have htail : ∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.current.vtag (args.tail.get i))) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using hargs i.succ
  obtain ⟨ht⟩ := ih args.tail htail
  have hhead : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (RawReflexivityDispatcher.valid I.current.vtag args.head)) := by
   simpa only [List.Vector.get_zero] using hargs 0
  obtain ⟨hh⟩ := hhead
  obtain ⟨hp⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I G args.head (tupleValue (tags I) args.tail.toList) hh ht
  rw [TupleStructureProof.succ]
  exact ConstructorValidityProof.unary p f lhs rhs t old arithmetic x I G false _ hp
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleValidityProof
