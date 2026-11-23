module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBareFreeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalAccessibilityIntroduction)
open ID1Completion.InternalComputabilityDownwardProof (edgeCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalAtomicMembershipSyntaxProof (underSuccessor membershipRename moveFree)
open NumberedWindowInternalAtomicRefinementObjectChecks (exact_OpenRefinedAtomicAcceptance)
open NumberedWindowInternalAuxBottomRefinementObjectChecks (exact_OpenAuxBottomForgets)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules exact_DomainRules)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
  (literalNeutral neutralWithCarrier exact_OpenLiteralNeutralBottomI)

private theorem acceptsGraph {α : Type} (r : Program 3) (x w y : OTerm α) :
    accepts r x w y = programGraph r (suc z) ![x,w,y] := rfl

attribute [local irreducible] programGraph

/-- The actual original bare free variable is accessible at any held
window type in the same augmented body. Its only genuine successors
are the already-paid bare bottom at the same context and type. -/
theorem exact_OpenLiteralNeutralBareFreeI (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x ctx ty name : OTerm α)
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal x (packedFreeTerm ctx ty name))))
    (held : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (carrier (literalNeutral i r) false c x))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (membership false x)) := by
  let R := augmented i (neutralWithCarrier i r)
  let S := literalNeutral i r
  let B := sourceBody S c
  apply actualOriginalAccessibilityIntroduction S false c α Γ x held
  let j : α → α ⊕ Fin 1 := Sum.inl
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H := edge S false c (x.relabel j) y
  let A := H :: Γ.map weaken
  have fA := moveFree x ctx ty name j (underSuccessor Γ H) shape
  have once : Nonempty (Derivation B A (membership false y)) := by
    apply edgeCases S c (x.relabel j) y _ ⟨Derivation.hypothesis (List.mem_cons_self : H ∈ A)⟩
    intro β ρ Δ w keep cert
    rw [membershipRename]
    let x' := (x.relabel j).relabel ρ
    let ctx' := (ctx.relabel j).relabel ρ
    let ty' := (ty.relabel j).relabel ρ
    let name' := (name.relabel j).relabel ρ
    let y' := y.relabel ρ
    have known := moveFree (x.relabel j) (ctx.relabel j) (ty.relabel j) (name.relabel j) ρ keep fA
    have accepted := (exact_CertificateRules i (jRaw i) R (dCore i R permutation)
      false c B β Δ x' y' w).1 cert
    rw [acceptsGraph] at accepted
    have underlying := exact_OpenAuxBottomForgets i (refined i (neutralWithCarrier i r))
      B β Δ x' w y' accepted
    obtain ⟨b⟩ := exact_OpenRefinedAtomicAcceptance.1 i (neutralWithCarrier i r)
      B β Δ x' w y' ctx' ty' name' known underlying
    have cy := (exact_DomainRules i (jRaw i) R (dCore i R permutation)
      false c B β Δ y').2 ⟨Derivation.conjunctionRight b⟩
    exact exact_OpenLiteralNeutralBottomI i r c β Δ y' ctx' ty'
      ⟨Derivation.conjunctionLeft b⟩ cy
  obtain ⟨out⟩ := once
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction out)⟩

#print axioms exact_OpenLiteralNeutralBareFreeI
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBareFreeProof
