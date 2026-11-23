module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressOpenCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAddressRankZeroRawProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardForgetsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankPartitionZeroCertificateProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowComputabilityFormulaTargets (accepts)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalRankUniversalCarrier (completeRankEven alwaysCarried)
open NumberedWindowInternalNeutralRankGuardForgetsProof (exact_OpenRankEvenForgets)
open NumberedWindowInternalNeutralRankGuardApplicationProof (targetReport)
open NumberedWindowInternalAtomicRefinement (atTarget)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast addressGood)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)
open NumberedWindowInternalParameterizedAddressPositiveOpenProof (AddressAtReport)
open NumberedWindowInternalAddressRankZeroRawProof
open NumberedWindowInternalRankPartitionedAddress
open NumberedWindowInternalRankPartitionedAddressOpenCasesProof

private theorem acceptsGraph {α : Type} (r : Program 3) (x w y : OTerm α) :
    accepts r x w y = programGraph r (suc z) ![x,w,y] := rfl

attribute [local irreducible] programGraph

private theorem fromCertificate (i j g : Program 1) (r d : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (x w y : OTerm α) :
    let R := completeRankEven i g r
    let S := data i j R d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (certificate S false c x y w)) →
    Nonempty (Derivation B Γ (programGraph r (suc z) ![x,w,y])) ∧
      Nonempty (Derivation B Γ (unary i (suc z) y)) := by
  intro R S B accepted
  have supplied := (exact_CertificateRules i j R d false c B α Γ x y w).1 accepted
  have carried := exact_OpenRankEvenForgets i g (alwaysCarried i r) x w y supplied
  rw [acceptsGraph] at carried
  obtain ⟨actual⟩ := conjunctionRecover r (atTarget i) ![x,w,y] carried
  exact ⟨⟨Derivation.conjunctionLeft actual⟩,
    targetReport i x w y (suc z) ⟨Derivation.conjunctionRight actual⟩⟩

/-- From the actual complete-rank certificate and the original
address-rank-zero report at its destination, open the real zero
certificate fold in the same physical body. The true scalar test
supplies tag-three validity; no raw selector is presumed total by
numeric reflection. -/
theorem exact_OpenCompleteRankZeroCertificateCases
    (cv tv g j : Program 1) (W L d : Program 3) (raw : Program 5) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x w y : OTerm α) (goal : Formula α) :
    let i := addressScalar cv tv W L
    let r := rankPartitionedAddress cv tv g raw L
    let R := completeRankEven i (addressRank g) r
    let S := data i j R d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (certificate S false c x y w)) →
    Nonempty (Derivation B Γ (unary (addressRank g) z y)) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (ctx ty src dst : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      Nonempty (Derivation B Δ (AddressAtReport cv tv (zeroPositive g raw L)
        (x.relabel ρ) (w.relabel ρ) (y.relabel ρ) ctx ty src dst)) →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal) := by
  intro i r R S B accepted rank next
  have held := fromCertificate i j (addressRank g) r d c x w y accepted
  have valid := exact_OpenPhysicalScalarAddressGood cv tv W L y held.2
  apply programCases rawLeast ![y] goal
  intro β ρ Δ k keep field
  rw [inputsRename] at field
  have okay := renameInto valid ρ Δ keep
  have rz := renameInto rank ρ Δ keep
  rw [unaryRename,sucRelabel,zRelabel] at okay
  rw [unaryRename,zRelabel] at rz
  have rawZero := exact_OpenRawRankFromAddressZero g (y.relabel ρ) k okay field rz
  have checked := renameInto held.1 ρ Δ keep
  rw [graph3Rename,sucRelabel,zRelabel] at checked
  apply exact_OpenRankPartitionZeroCases cv tv g raw L (x.relabel ρ) (w.relabel ρ) (y.relabel ρ)
    k (goal.relabel ρ) field rawZero checked
  intro γ ι Δ' ctx ty src dst keep' report _
  have rel (f : Formula α) : (f.relabel ρ).relabel ι = f.relabel (ι ∘ ρ) := formulaRelabelComposition ρ ι f
  have keepBoth : ∀ f ∈ Γ, f.relabel (ι ∘ ρ) ∈ Δ' := by
    intro f hf
    rw [← rel f]
    exact keep' (f.relabel ρ) (keep f hf)
  have out := next γ (ι ∘ ρ) Δ' ctx ty src dst keepBoth (by simpa only [Term.relabel_relabel] using report)
  simpa only [rel] using out

#print axioms exact_OpenCompleteRankZeroCertificateCases
end LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankPartitionZeroCertificateProof
