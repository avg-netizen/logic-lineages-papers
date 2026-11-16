module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.EqualityCapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem equality {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (pF pR : Program 1) (I : JointInstallation (root f lhs rhs pF pR old a x) f lhs rhs t old a (SaturatedAxiomLeaf.saturated x)) :
 EqualityCapability f lhs rhs t old a x pF pR I := by
 let p := root f lhs rhs pF pR old a x
 intro ctx raw index fuel
 obtain ⟨he⟩ := CumulativeUniformRule12Registry.CapabilityProof.equality p f lhs rhs t old a (SaturatedAxiomLeaf.saturated x) I.previous ctx raw index fuel
 let formula := RawEqualityInstantiation.formulaValue I.previous.previous.previous.previous.current.ctag I.previous.previous.previous.previous.current.atag lhs rhs raw
 obtain ⟨hr⟩ := CapabilitySupport.retentionInternal p f lhs rhs t old a (SaturatedAxiomLeaf.saturated x) I index fuel .zero (.add formula formula)
  (RawEqualityInstantiationCertificate.certificate I.previous.previous.previous.previous.current.ctag I.previous.previous.previous.previous.current.qtag raw)
 exact CapabilitySupport.inSource f lhs rhs pF pR old a x _ ⟨Hilbert.compose hr he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.EqualityCapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.EqualityCapabilityProof
