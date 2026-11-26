module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.PropositionalCapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem propositional {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : PropositionalCapability f lhs rhs t old a baseX pF pR I := by
 intro isS ctx rawA rawB rawC index fuel
 cases isS with
 | false =>
  exact CapabilitySupport.inSource f lhs rhs pF pR old a baseX _
   (UniformClosedPropositionalCertificate.StatementChecks.exactCertificate 4 _ _ _ _ false I.currentK ctx rawA rawB rawC index fuel)
 | true =>
  exact CapabilitySupport.inSource f lhs rhs pF pR old a baseX _
   (UniformClosedPropositionalCertificate.StatementChecks.exactCertificate 4 _ _ _ _ true I.currentS ctx rawA rawB rawC index fuel)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.PropositionalCapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.PropositionalCapabilityProof
