module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.RuntimeInterface
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
variable {n k : Nat} {p : Program n} {f : Formula 1} {lhs rhs : Term 1} {t : Term k}
 {old ar : Program 1} {x : Program 3}
def tags (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x) : CurrentRecursionBaseProgram.Tags where
 ptag := I.currentK.ptag
 ctag := I.previous.previous.current.ctag
 atag := I.previous.previous.current.atag
 ntag := I.previous.previous.previous.previous.previous.numeralTag
 mtag := I.previous.previous.previous.previous.previous.mpTag
 r12 := I.previous.current.constructorTag
 r13 := I.previous.previous.current.constructorTag
 baseTag := 0
 childTag := 0
/-- Only the six used primitive fields are installed. No dummy evaluator/child
memberships are asserted for this nonrecursive alias producer. -/
theorem installed (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x) :
 CurrentBasicProducerProgram.Installation p (tags I) :=
 ⟨I.currentK.h_ptag,I.previous.previous.current.h_ctag,I.previous.previous.current.h_atag,
  I.previous.previous.previous.previous.previous.hnumeral,I.previous.previous.previous.previous.previous.hmp,
  I.previous.previous.current.h_constructor⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.RuntimeInterface
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.RuntimeInterface
