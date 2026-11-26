module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginPoolProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph poolOccurrence)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (binder occurrenceUnfold)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverRename)
open NumberedWindowInternalSparseCoverOccurrenceTargets
open NumberedWindowInternalSparseSeedOriginTargets
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeastOpenChecks (exact_OpenPackedLeastPoolOccurrence)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)

private theorem forgetContextAndPool (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (paid : ExactRetainedPredecessor) {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (ctx ty seed k : OTerm α)
    (supplied : Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed k))) :
    Nonempty (Derivation body Γ (occursInCover C s seed seed)) := by
  rw [occurrenceUnfold] at supplied
  obtain ⟨both⟩ := supplied
  let a := binder C X W s ctx ty seed k
  let Δ := existsOne a :: Γ.map weaken
  let Θ := a :: Δ.map weaken
  let lift (t : OTerm α) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) :=
    (t.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl
  let pool : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  have atPool : Derivation body Θ a := Derivation.hypothesis List.mem_cons_self
  have evidence := Derivation.conjunctionRight atPool
  obtain ⟨source⟩ := NumberedWindowInternalSparseSeedOriginPoolProof.recover C X W s paid
    (lift ctx) (lift ty) (lift seed) pool (lift k) ⟨Derivation.conjunctionLeft evidence⟩
    ⟨Derivation.conjunctionRight evidence⟩
  have endResult : Derivation body Θ (weaken (weaken (occursInCover C s seed seed))) := by
    change Derivation body Θ (((occursInCover C s seed seed).relabel
      (Sum.inl : α → α ⊕ Fin 1)).relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1))
    rw [coverRename,coverRename]
    exact source
  have withPayload : Derivation body Δ (weaken (occursInCover C s seed seed)) :=
    Derivation.existentialElimination (Derivation.hypothesis List.mem_cons_self) endResult
  exact ⟨Derivation.existentialElimination both withPayload⟩

private theorem atCover (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (ctx ty seed k : OTerm α)
    (least : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed k)))
    (cover : Derivation body Γ (occursInCover C s seed seed)) :
    Nonempty (Derivation body Γ (ltF seed k).not) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let vertices : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := coverRow C s (seed.relabel j) (seed.relabel j) vertices
  let Δ := row :: Γ.map weaken
  have data : Derivation body Δ row := Derivation.hypothesis List.mem_cons_self
  have run := renameInto least j Δ (fun p h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩))
  rw [leastRename] at run
  let xs : Fin 3 → OTerm (α ⊕ Fin 1) := ![ctx.relabel j,ty.relabel j,seed.relabel j]
  have actual : Nonempty (Derivation body Δ (programGraph (poolAtSeed C s) vertices xs)) := by
    apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) vertices xs ![xs 2]
      ⟨Derivation.conjunctionLeft data⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 xs
  obtain ⟨r⟩ := run
  obtain ⟨a⟩ := actual
  obtain ⟨bound⟩ := NumberedWindowInternalSparseSeedBoundChecks.exact_PackedSeedBound C X W s body _ Δ
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) vertices (k.relabel j)
  have doneAt := Derivation.implicationElimination bound
    (Derivation.conjunctionIntroduction r (Derivation.conjunctionIntroduction a (Derivation.conjunctionRight data)))
  have final : Derivation body Δ (weaken (ltF seed k).not) := by
    change Derivation body Δ ((ltF seed k).relabel j).not
    rwa [orderRename]
  exact ⟨Derivation.existentialElimination cover final⟩

theorem exact_RoundSeedOrigin : ExactRoundSeedOrigin :=
  NumberedWindowInternalSparseSeedOriginInductionProof.roundSource

theorem exact_SuccessfulSeedBound : ExactSuccessfulSeedBound := by
  intro paid C X W s body α Γ ctx ty seed k
  let A := leastGraph C X W s ctx ty seed k
  have run : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨pool⟩ := exact_OpenPackedLeastPoolOccurrence body α (A :: Γ) C X W s ctx ty seed k
  obtain ⟨source⟩ := forgetContextAndPool C X W s paid ctx ty seed k ⟨Derivation.implicationElimination pool run⟩
  obtain ⟨bound⟩ := atCover C X W s ctx ty seed k ⟨run⟩ source
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction source bound)⟩

#print axioms exact_RoundSeedOrigin
#print axioms exact_SuccessfulSeedBound
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginChecks
