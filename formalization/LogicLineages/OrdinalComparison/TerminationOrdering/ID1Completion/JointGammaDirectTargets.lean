module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDirectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDirectTargets
open Source JointGammaQuotient

/-- The original occurrence-index/path test, joint in Gamma. Repeated removed indices
are permitted; extra or missing certificates and failed indices are rejected. -/
def ActualJointDominationPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Parameters n × List Nat × List Nat × List QuotientDominationCertificates.Entry =>
    QuotientDominationCertificates.test n arity p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2
      p.2.1 p.2.2.1 p.2.2.2)

/-- The original direct multiset checker, with its exact two permutation guards
and nonempty removed-list requirement, joint in Gamma and every other datum. -/
def ActualJointDirectPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Parameters n × List Nat × List Nat × QuotientDirectCertificates.Certificate =>
    QuotientDirectCertificates.directTest n arity p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2
      p.2.1 p.2.2.1 p.2.2.2)

/-- The original numeric direct-multiset test on the unchanged Encodable codes.
No source/target/certificate validity premise; malformed codes still return false. -/
def ActualJointNumericDirectPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Parameters n × Nat × Nat × Nat =>
    QuotientDirectCertificates.numericTest n arity p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2
      p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDirectTargets
