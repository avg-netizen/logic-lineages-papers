module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem trace {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX) installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 SpecializationTraceCapability installed lhs rhs t old a baseX pF pR c I := by
 intro n f sigma ctx
 have h := PrescribedRuntimeSpecialization.StatementChecks.exactPrescribedTrace
  4 (root installed lhs rhs pF pR old a baseX)
  (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  I.previous.previous.current I.previous.previous.previous.previous.previous.mpTag
  I.previous.previous.previous.previous.previous.hmp n f sigma ctx (PrescribedSourceAxiomSpecialization.seed f)
 exact CapabilitySupport.inSource installed lhs rhs pF pR old a baseX _ h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedTraceProof
