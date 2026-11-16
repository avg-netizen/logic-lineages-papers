module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Uniform13CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CapabilitySupport
theorem uniform13 {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Uniform13Capability f lhs rhs t old a baseX pF pR I := by
 intro ctx formula replacement index fuel
 let p := root f lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let A := UniformClosedInstanceRecognizer.guards I.previous.previous.current.fval I.previous.previous.current.vtag formula replacement
 let C := UniformClosedRule13.conclusionValue I.previous.previous.current.caseTag I.previous.previous.current.predTag I.previous.previous.current.ctag formula replacement
 let code := UniformClosedRule13Certificate.certificate I.previous.previous.current.ctag I.previous.previous.current.constructorTag formula replacement
 obtain ⟨hcert⟩ := CumulativeUniformRule12Registry.CapabilityProof.uniform13 p f lhs rhs t old a _ I.previous ctx formula replacement index fuel
 have hh : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hall := Hilbert.Local.mp (.base hcert) hh
 have hcore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hall
 obtain ⟨hret⟩ := retentionInternal p f lhs rhs t old a _ I index fuel .zero (.add C C) code
 have hnew := Hilbert.Local.mp (.base hret) hcore
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.currentK.verifierTag I.currentK.coreTag
  (UniformClosedPropositionalCertificate.checker (previousLogical f lhs rhs old) (arithmetic a) (SaturatedAxiomLeaf.saturated baseX))
  I.currentK.h_verifierTag I.currentK.h_coreTag index fuel .zero (.add C C) code
 have hfuel := Hilbert.Local.mp (.base hinj) hnew
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (.base (.logical (.andIntro _ _))) hnew) hfuel
 exact inSource f lhs rhs pF pR old a baseX _ ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Uniform13CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Uniform13CapabilityProof
