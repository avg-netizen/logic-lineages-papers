module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgePoolProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph poolOccurrence)
open NumberedWindowInternalSparsePackedLeastOpenChecks (exact_OpenPackedLeastPoolOccurrence)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename binder occurrenceUnfold)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverRename)
open NumberedWindowInternalSparseMinimumEdgePoolProof (packedClosure acceptedEdgeRename)
open NumberedWindowInternalSparsePackedBoundChecks (exact_OpenPackedLeastLowerBound)
open NumberedWindowInternalSparseMinimumEdgeTargets

theorem exact_PackedMembersClosure : ExactPackedMembersClosure := packedClosure

private theorem boundFromOccurrence (pred : ExactRetainedPredecessor)
    (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (ctx ty seed k target : OTerm α)
    (observed : Derivation body Γ (leastGraph C X W s ctx ty seed k ⊓
      (acceptEdge (edge4 X W) ctx ty k target ⊓ occursInCover C s seed target)))
    (poolHit : Derivation body Γ (poolOccurrence C X W s ctx ty seed k)) :
    Nonempty (Derivation body Γ (ltF target k).not) := by
  rw [occurrenceUnfold] at poolHit
  let a := binder C X W s ctx ty seed k
  let Δ := existsOne a :: Γ.map weaken
  let Θ := a :: Δ.map weaken
  let j : α → α ⊕ Fin 1 := Sum.inl
  let l : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 := Sum.inl
  let lift (t : OTerm α) := (t.relabel j).relabel l
  let pool : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  have atPool : Derivation body Θ a := Derivation.hypothesis List.mem_cons_self
  have row := Derivation.conjunctionRight atPool
  have first := renameInto ⟨observed⟩ j Δ (fun p hp =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  simp only [conjunctionRename,leastRename,acceptedEdgeRename,coverRename] at first
  have second := renameInto first l Θ (fun p hp =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  simp only [conjunctionRename,leastRename,acceptedEdgeRename,coverRename] at second
  obtain ⟨lifted⟩ := second
  obtain ⟨close⟩ := exact_PackedMembersClosure pred C X W s body _ Θ (lift ctx) (lift ty)
    (lift seed) pool (lift k) (lift target)
  have next := Derivation.implicationElimination close
    (Derivation.conjunctionIntroduction row (Derivation.conjunctionRight lifted))
  obtain ⟨bound⟩ := exact_OpenPackedLeastLowerBound C X W s body _ Θ (lift ctx) (lift ty)
    (lift seed) pool (lift target) (lift k)
  have answer := Derivation.implicationElimination bound (Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft lifted) (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft row) next))
  have result : Derivation body Θ (weaken (weaken (ltF target k).not)) := by
    change Derivation body Θ (((ltF target k).relabel j).relabel l).not
    rwa [orderRename,orderRename]
  have one : Derivation body Δ (weaken (ltF target k).not) :=
    Derivation.existentialElimination (Derivation.hypothesis List.mem_cons_self) result
  exact ⟨Derivation.existentialElimination poolHit one⟩

theorem exact_MinimumEdgeBound : ExactMinimumEdgeBound := by
  intro pred C X W s body α Γ ctx ty seed k target
  let A := leastGraph C X W s ctx ty seed k ⊓ (acceptEdge (edge4 X W) ctx ty k target ⊓
    occursInCover C s seed target)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨occurs⟩ := exact_OpenPackedLeastPoolOccurrence body α Δ C X W s ctx ty seed k
  obtain ⟨result⟩ := boundFromOccurrence pred C X W s ctx ty seed k target h
    (Derivation.implicationElimination occurs (Derivation.conjunctionLeft h))
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_PackedMembersClosure
#print axioms exact_MinimumEdgeBound
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeChecks
