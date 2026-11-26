module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.SyntaxProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
theorem projectionMember {arity n : Nat} (root : Program arity) (p : Program 1) (q : Program n)
 (tag : Nat) (h : (nodes root)[tag]? = some ⟨1,GorbowNamedInternalProvability.augment p q⟩) :
 GorbowStandardInduction.universalClosure (projectionFormula tag) ∈ axioms root := by
 have hp := SixSol20261112.Fuel.Equations.functionChild root tag (.projection (0 : Fin 2)) (branches p q) h
 apply EffectiveNumeral.NodeSupport.intoRegistry (.projection (0 : Fin 2)) arity root (tag+1) hp
 apply EffectiveNumeral.NodeSupport.rootIncluded
 exact List.mem_singleton.mpr rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.SyntaxProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.SyntaxProof
