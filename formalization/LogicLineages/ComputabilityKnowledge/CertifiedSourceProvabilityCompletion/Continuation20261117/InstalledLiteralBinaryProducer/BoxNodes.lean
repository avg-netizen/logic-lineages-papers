module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxNodes
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
theorem nodes {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF0 pR : Program 1) (pCK : Program 2) (box : Program 6) :
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 (GorbowPRRegistry.nodes root)[6]? = some ⟨1,augmented pF q⟩ ∧
 (GorbowPRRegistry.nodes root)[8]? = some ⟨1,pF⟩ ∧
 (GorbowPRRegistry.nodes root)[10]? = some ⟨1,GorbowNamedInternalProvability.augment pF0 pCK⟩ ∧
 (GorbowPRRegistry.nodes root)[12]? = some ⟨1,pF0⟩ := by
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 have h6 : (GorbowPRRegistry.nodes root)[6]? = some ⟨1,augmented pF q⟩ :=
  GorbowSourceRegistryPadding.Proof.functionRoot (augmented pF q) pR
 have h8 : (GorbowPRRegistry.nodes root)[8]? = some ⟨1,pF⟩ :=
  RetainedBaseProducerInstallation.RegistryProof.firstChild root 6 pF q h6
 have h10 : (GorbowPRRegistry.nodes root)[10]? = some ⟨1,inner⟩ :=
  RetainedBaseProducerInstallation.RegistryProof.firstChild root 8 inner box h8
 have h12 : (GorbowPRRegistry.nodes root)[12]? = some ⟨1,pF0⟩ :=
  RetainedBaseProducerInstallation.RegistryProof.firstChild root 10 pF0 pCK h10
 exact ⟨h6,h8,h10,h12⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxNodes
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxNodes
