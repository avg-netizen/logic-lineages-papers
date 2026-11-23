module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardForgetsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierObjectProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalComputabilityDownwardProof (edgeCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules exact_CertificateRules)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalAtomicRefinement (atTarget)
open NumberedWindowInternalNeutralRankGuardForgetsProof (exact_OpenRankEvenForgets)
open NumberedWindowInternalNeutralRankGuardApplicationProof (targetReport)
open NumberedWindowInternalRankUniversalCarrier

private theorem acceptsGraph {α : Type} (r : Program 3) (x w y : OTerm α) :
    accepts r x w y = programGraph r (suc z) ![x,w,y] := rfl

attribute [local irreducible] programGraph

theorem exact_OpenCompleteRankCertificateCarrier (i j g : Program 1) (r d : Program 3)
    (c : Nat) (α : Type) (Γ : List (Formula α)) (x w y : OTerm α) :
    let R := completeRankEven i g r
    let S := data i j R d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (certificate S false c x y w)) →
    Nonempty (Derivation B Γ (carrier S false c y)) := by
  intro R S B accepted
  have supplied := (exact_CertificateRules i j R d false c B α Γ x y w).1 accepted
  have carried := exact_OpenRankEvenForgets i g (alwaysCarried i r) x w y supplied
  rw [acceptsGraph,alwaysCarried] at carried
  obtain ⟨actual⟩ := conjunctionRecover r (atTarget i) ![x,w,y] carried
  exact (exact_DomainRules i j R d false c B α Γ y).2
    (targetReport i x w y (suc z) ⟨Derivation.conjunctionRight actual⟩)

/-- On the exact new body, every actual even edge has a genuine target
carrier, regardless of the rank or shape of its source. -/
theorem exact_OpenCompleteRankEdgeCarrier (i j g : Program 1) (r d : Program 3)
    (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α) :
    let R := completeRankEven i g r
    let S := data i j R d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (edge S false c x y)) →
    Nonempty (Derivation B Γ (carrier S false c y)) := by
  intro R S B held
  apply edgeCases S c x y _ held
  intro β ρ Δ w _ actual
  rw [carrierRename]
  exact exact_OpenCompleteRankCertificateCarrier i j g r d c β Δ
    (x.relabel ρ) w (y.relabel ρ) actual

#print axioms exact_OpenCompleteRankCertificateCarrier
#print axioms exact_OpenCompleteRankEdgeCarrier
end LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierObjectProof
