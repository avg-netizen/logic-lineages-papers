module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SourceEndpoint
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence

/-- Constructed from the primitive base BEFORE selecting the enlarged source.
Neither the final pF AST nor its size occurs in this fixed finite construction. -/
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF0 : Program 1) : Program 6 :=
 ReflexivityInstalled.bundle
  [⟨6,CumulativePropositionalSource.extra f lhs rhs t old a baseX⟩,
   ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩,
   ⟨3,RuntimeOffsetAugmentationProducer.program⟩]

def selected {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF0 : Program 1) (pCK : Program 2) (pG : Program 6) : Program 1 :=
 GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK)
  (InstalledProducerExtra.container pG (extra f lhs rhs t old a baseX pF0))

def AcceptedPeel {n ctx : Nat} (K : PrescribedRuntimeCallCongruence.Tags)
 (coreTag verifierTag producerTag target : Nat) (p : Program 1) (q : Program n)
 (index value fuel : Term ctx) : Formula ctx :=
 accepted coreTag verifierTag index fuel
  (equalValue K.ctag K.atag (CorrectedAugmentationErasure.left K target value)
   (CorrectedAugmentationErasure.right K p q target value))
  (call producerTag (Term.numeral target ::ᵥ
   Term.numeral (argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 1) ::ᵥ value ::ᵥ nil))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation
