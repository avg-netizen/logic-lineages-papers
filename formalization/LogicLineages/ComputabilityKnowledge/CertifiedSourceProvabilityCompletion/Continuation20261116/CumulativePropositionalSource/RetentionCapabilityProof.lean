module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RetentionCapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CapabilitySupport
theorem retention {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : RetentionCapability f lhs rhs t old a baseX pF pR I := by
 intro ctx index fuel context formula code
 exact inSource f lhs rhs pF pR old a baseX _
  (retentionInternal _ f lhs rhs t old a _ I index fuel context formula code)
theorem priorRetention {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : PriorRetentionCapability f lhs rhs t old a baseX pF pR I := by
 intro ctx index fuel context formula code
 obtain ⟨hprior⟩ := CumulativeUniformRule12Registry.CapabilityProof.retention
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a _ I.previous ctx index fuel context formula code
 obtain ⟨hnew⟩ := retentionInternal (root f lhs rhs pF pR old a baseX) f lhs rhs t old a _ I index fuel context formula code
 exact inSource f lhs rhs pF pR old a baseX _ ⟨Hilbert.compose hnew hprior⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RetentionCapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RetentionCapabilityProof
