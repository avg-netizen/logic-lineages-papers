module
public import LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshMembershipProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalFreshProbeEmitter (chooseFresh)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeEmitterObjectChecks (exact_SelectedFreshOpenShape)
open NumberedWindowInternalFreshProbeParsedEmitter (selected)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)
open NumberedWindowInternalAtomicMembershipChecks (exact_RefinedAtomicMembership)
open NumberedWindowInternalGroundFreshTargets

theorem givenFreshMember : ExactGivenPackedFreshMembership := by
  intro i j r d v context α Γ q u
  dsimp only
  intro actual scalar
  let S := data i j (refined i r) d
  let B := sourceBody S context
  let p := selected v.scalarProg v.freshBound
  have actualA : Nonempty (Derivation B Γ (freshAt (chooseFresh p) q u)) := actual
  have shape := exact_SelectedFreshOpenShape p B α Γ q u actualA
  let β := α ⊕ Fin 3
  let lift : α → β := Sum.inl
  let q' := q.relabel lift
  let u' := u.relabel lift
  let c : OTerm β := .var (.inr 0)
  let t : OTerm β := .var (.inr 1)
  let n : OTerm β := .var (.inr 2)
  let matrix := programGraph p.context c ![q'] ⊓ (programGraph p.domain t ![q'] ⊓
    (programGraph p.name n ![q'] ⊓ equal u' (packedFreeTerm c t n)))
  change Nonempty (Derivation B Γ (block matrix)) at shape
  apply actualFiniteExistentialElimination B α 3 Γ matrix (membership false u) shape
  let Δ := matrix :: Γ.map (fun A => A.relabel lift)
  have preserves : ∀ A ∈ Γ, A.relabel lift ∈ Δ :=
    fun A h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨A,h,rfl⟩)
  have carried := renameInto scalar lift Δ preserves
  rw [carrierRename] at carried
  have facts : Derivation B Δ matrix := Derivation.hypothesis List.mem_cons_self
  have e : Nonempty (Derivation B Δ (equal u' (packedFreeTerm c t n))) :=
    ⟨Derivation.conjunctionRight
      (Derivation.conjunctionRight (Derivation.conjunctionRight facts))⟩
  rw [membershipRename]
  exact (exact_RefinedAtomicMembership.2 i j r d context β Δ u' c t n e).mp carried

end LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshMembershipProof
