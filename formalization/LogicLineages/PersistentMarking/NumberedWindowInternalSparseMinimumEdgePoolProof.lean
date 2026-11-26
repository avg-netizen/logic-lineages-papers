module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersClosureChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgePoolProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDirectedRounds (members membersTape)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed membersAtSeed)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRoundsInclusionTargets (MembersIncluded)
open NumberedWindowInternalSparseCoverOccurrenceTargets
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverIntro coverRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)

open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseMembersClosureChecks (exact_MembersEdgeClosure)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseMinimumEdgeTargets
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem poolArgs (C : Program 3) (s : Settings) (xs : Fin 3 → OTerm α)
    (vertices : OTerm α) (hv : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices (xs 2))))
    (k : Fin 4) :
    Nonempty (Derivation body Γ (programGraph
      ((![poolAtSeed C s,.projection 0,.projection 1,.projection 2] : Fin 4 → Program 3) k)
      (membersTape vertices (xs 0) (xs 1) (xs 2) k) xs)) := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2)
      vertices xs ![xs 2] hv
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 xs
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero c
    exact projectionValue 2 xs


theorem acceptedEdgeRename {α β : Type} (E : Program 4) (ctx ty w k : OTerm α) (j : α → β) :
    (acceptEdge E ctx ty w k).relabel j = acceptEdge E (ctx.relabel j) (ty.relabel j)
      (w.relabel j) (k.relabel j) := by
  simp only [acceptEdge,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

private theorem fromCover (pred : ExactRetainedPredecessor) (C : Program 3) (X : Program 2)
    (W : Program 3) (s : Settings) (ctx ty seed pool source target : OTerm α)
    (selected : Nonempty (Derivation body Γ
      (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ memberGraph pool source)))
    (edge : Nonempty (Derivation body Γ (acceptEdge (edge4 X W) ctx ty source target)))
    (cover : Derivation body Γ (occursInCover C s seed target)) :
    Nonempty (Derivation body Γ (memberGraph pool target)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let vertices : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := coverRow C s (seed.relabel j) (target.relabel j) vertices
  let Δ := row :: Γ.map weaken
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have actual : Derivation body Δ row := Derivation.hypothesis List.mem_cons_self
  have ss := renameInto selected j Δ keep
  simp only [conjunctionRename,programRename,tripleInputsRename,graphRename] at ss
  have ee := renameInto edge j Δ keep
  rw [acceptedEdgeRename] at ee
  obtain ⟨ss⟩ := ss
  obtain ⟨ee⟩ := ee
  let xs := ![ctx.relabel j,ty.relabel j,seed.relabel j]
  let ys := membersTape vertices (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨computed⟩ := compositionRecover (members (edge4 X W))
    ![poolAtSeed C s,.projection 0,.projection 1,.projection 2] (pool.relabel j) xs ys
    ⟨Derivation.conjunctionLeft ss⟩ (poolArgs C s xs vertices ⟨Derivation.conjunctionLeft actual⟩)
  obtain ⟨extend⟩ := exact_MembersEdgeClosure pred (edge4 X W) body _ Δ vertices (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) (pool.relabel j) (source.relabel j) (target.relabel j)
  have step := Derivation.implicationElimination extend (Derivation.conjunctionIntroduction computed
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionRight ss) ee)
      (Derivation.conjunctionRight actual)))
  have result : Derivation body Δ (weaken (memberGraph pool target)) := by
    change Derivation body Δ ((memberGraph pool target).relabel j)
    rwa [graphRename]
  exact ⟨Derivation.existentialElimination cover result⟩

theorem packedClosure : ExactPackedMembersClosure := by
  intro pred C X W s body α Γ ctx ty seed pool source target
  let selected := programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ memberGraph pool source
  let edge := acceptEdge (edge4 X W) ctx ty source target ⊓ occursInCover C s seed target
  let Δ := (selected ⊓ edge) :: Γ
  have h : Derivation body Δ (selected ⊓ edge) := Derivation.hypothesis List.mem_cons_self
  have e := Derivation.conjunctionRight h
  obtain ⟨k⟩ := fromCover pred C X W s ctx ty seed pool source target ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft e⟩ (Derivation.conjunctionRight e)
  exact ⟨Derivation.implicationIntroduction k⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgePoolProof
