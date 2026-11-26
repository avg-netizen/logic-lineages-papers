module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.RegistryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence


theorem preserved {n : Nat} (p : Program 1) (q : Program n) (entry : Packed)
 (h : Occurs entry p) : Occurs entry (GorbowNamedInternalProvability.augment p q) :=
 .compositionArgument _ _ (0 : Fin 2) h

theorem inserted {n : Nat} (p : Program 1) (q : Program n) :
 Occurs ⟨n,q⟩ (GorbowNamedInternalProvability.augment p q) := by
 have h : Occurs ⟨n,q⟩ (GorbowNamedInternalProvability.wrapper q) :=
  .compositionFunction _ _ (.here q rfl)
 exact .compositionArgument _ _ (1 : Fin 2) h

theorem inSource (pF pR : Program 1) (q : Program 5) (entry : Packed)
 (h : Occurs entry pF) :
 Occurs entry (GorbowSourceRegistryPadding.root (augmented pF q) pR) := by
 have hq : Occurs entry (augmented pF q) := preserved pF q entry h
 have hw : Occurs entry (GorbowSourceRegistryPadding.wrapper (augmented pF q)) :=
  .compositionFunction _ _ hq
 exact .compositionArgument _ _ (3 : Fin 5) hw

theorem firstChild {arity n : Nat} (root : Program arity) (tag : Nat)
 (p : Program 1) (q : Program n)
 (h : (nodes root)[tag]? = some ⟨1,GorbowNamedInternalProvability.augment p q⟩) :
 (nodes root)[tag+2]? = some ⟨1,p⟩ := by
 exact SixSol20261112.Fuel.Equations.argumentChild root tag (.projection (0 : Fin 2))
  (CorrectedAugmentationErasure.branches p q) h 0

theorem containerExtra {arity n : Nat} (root : Program arity) (tag : Nat)
 (pG : Program 6) (extra : Program n)
 (h : (nodes root)[tag]? = some ⟨6,InstalledProducerExtra.container pG extra⟩) :
 (nodes root)[InstalledProducerExtra.producerTag tag pG extra]? = some ⟨6,pG⟩ ∧
 (nodes root)[InstalledProducerExtra.extraTag tag pG extra]? = some ⟨n,extra⟩ := by
 have hp := SixSol20261112.Fuel.Equations.argumentChild root tag
  (.projection (0 : Fin 2)) (InstalledProducerExtra.containerArguments pG extra) h 0
 have hw := SixSol20261112.Fuel.Equations.argumentChild root tag
  (.projection (0 : Fin 2)) (InstalledProducerExtra.containerArguments pG extra) h 1
 have he := SixSol20261112.Fuel.Equations.functionChild root
  (tag + argumentTag (.projection (0 : Fin 2)) (InstalledProducerExtra.containerArguments pG extra) 1)
  extra (fun _ => .projection (0 : Fin 6)) hw
 exact ⟨hp,he⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.RegistryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.RegistryProof
