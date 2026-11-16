module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootEncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open PrescribedRuntimeCallCongruence
theorem call {arity k ctx n : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installed lhs rhs t old a x)
 (G : List (Formula ctx)) (tag : Term ctx) (args : List.Vector (Term ctx) n)
 (hargs : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (args.get i)))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (callValue (tags I) tag args))) := by
 let J := tags I
 obtain ⟨ht⟩ := TupleValidityProof.current p installed lhs rhs t old a x I G n args hargs
 obtain ⟨hn⟩ := PrescribedRuntimeCallCongruence.ValidityProof.closed p _ _ _ I.current G (Term.numeral n)
 obtain ⟨hv⟩ := PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.current J.numeralTag
  I.previous.previous.previous.previous.hnumeral G tag
 obtain ⟨hp⟩ := ConstructorValidityProof.pair p installed lhs rhs t old a x I G _ _ hv ht
 obtain ⟨hh⟩ := ConstructorValidityProof.pair p installed lhs rhs t old a x I G _ _ hn hp
 exact ConstructorValidityProof.unary p installed lhs rhs t old a x I G true _ hh
theorem previousNumeral {arity k ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installed lhs rhs t old a x)
 (G : List (Formula ctx)) (value : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag
   (LiteralNumeralPrefix.numeralCall (tags I).numeralTag value))) := by
 let J := I.previous.current
 obtain ⟨hscan⟩ := LiteralNumeralPrefix.StatementChecks.exactScan arity p (tags I).numeralTag J.stag J.ptag J.ctag
  I.previous.previous.previous.previous.hnumeral J.h_stag J.h_ptag J.h_ctag ctx value .zero .zero
 exact RawSuccCongruence.ValidityProof.localBinding p G J.vtag J.stag J.ptag J.ctag
  J.h_vtag J.h_stag J.h_ptag J.h_ctag (LiteralNumeralPrefix.numeralCall (tags I).numeralTag value) (.base hscan)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValidityProof
