module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceMembersProof
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

private theorem recover (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (inc : MembersIncluded (edge4 X W)) (ctx ty seed pool k : OTerm α)
    (selected : Nonempty (Derivation body Γ (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed])))
    (occurs : Nonempty (Derivation body Γ (memberGraph pool k))) :
    Nonempty (Derivation body Γ (occursInCover C s seed k)) := by
  apply programCases (scratchVertices C s) ![seed] _
  intro β j Δ vertices keep hv
  rw [coverRename]
  rw [unaryInputsRename] at hv
  have ss := renameInto selected j Δ keep
  rw [programRename,tripleInputsRename] at ss
  have mm := renameInto occurs j Δ keep
  rw [graphRename] at mm
  let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
  let ys := membersTape vertices (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  have computed := compositionRecover (members (edge4 X W))
    ![poolAtSeed C s,.projection 0,.projection 1,.projection 2] (pool.relabel j) xs ys
    ss (poolArgs C s xs vertices hv)
  obtain ⟨rule⟩ := inc body β Δ (pool.relabel j) vertices (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (k.relabel j)
  obtain ⟨c⟩ := computed
  obtain ⟨m⟩ := mm
  exact coverIntro C s (seed.relabel j) (k.relabel j) vertices hv
    ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction c m)⟩

theorem membersOccurrence : ExactMembersOccurrenceInCover := by
  intro C X W s inc body α Γ ctx ty seed pool k
  let P := programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ memberGraph pool k
  have h : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := recover C X W s inc ctx ty seed pool k
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceMembersProof
