module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceCoverProof

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverOccurrenceTargets (coverRow occursInCover)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseSeedOriginChecks (exact_SuccessfulSeedBound)
open NumberedWindowInternalSparsePackedSeedPresenceTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem suppliedCoverMember (C : Program 3) (s : Settings) (seed vertices : OTerm α)
    (source : Derivation body Γ (occursInCover C s seed seed))
    (actual : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed))) :
    Nonempty (Derivation body Γ (memberGraph vertices seed)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let covered : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := coverRow C s (seed.relabel j) (seed.relabel j) covered
  let Δ := row :: Γ.map weaken
  have existence : Derivation body Γ (existsOne row) := source
  have hit : Derivation body Δ row := Derivation.hypothesis List.mem_cons_self
  have supplied := renameInto actual j Δ
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [unaryRename] at supplied
  have same := valueUnique (scratchVertices C s) covered (vertices.relabel j) ![seed.relabel j]
    ⟨Derivation.conjunctionLeft hit⟩ supplied
  obtain ⟨present⟩ := headTransport scratchMember (suc z) covered (vertices.relabel j)
    ![seed.relabel j] same ⟨Derivation.conjunctionRight hit⟩
  have final : Derivation body Δ (weaken (memberGraph vertices seed)) := by
    change Derivation body Δ ((memberGraph vertices seed).relabel j)
    rwa [graphRename]
  exact ⟨Derivation.existentialElimination existence final⟩

theorem seedInGivenVertices : ExactSeedInGivenVertices := by
  intro C X W s body α Γ ctx ty seed minimum vertices
  let A := leastGraph C X W s ctx ty seed minimum ⊓ unary (scratchVertices C s) vertices seed
  let Δ := A :: Γ
  have given : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨origin⟩ := exact_SuccessfulSeedBound exact_RetainedPredecessor
    C X W s body α Δ ctx ty seed minimum
  have present := Derivation.conjunctionLeft
    (Derivation.implicationElimination origin (Derivation.conjunctionLeft given))
  obtain ⟨result⟩ := suppliedCoverMember C s seed vertices present ⟨Derivation.conjunctionRight given⟩
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceCoverProof
