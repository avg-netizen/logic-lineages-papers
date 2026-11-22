module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginPoolProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverIntro coverRename)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed membersAtSeed)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparseSeedOriginTargets
open NumberedWindowInternalSparseSeedOriginInductionProof (roundSource)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atLength (paid : ExactRetainedPredecessor) (X : Program 2) (W : Program 3)
    (ctx ty vertices seed out k : OTerm α)
    (guard : Nonempty (Derivation body Γ (memberGraph out k)))
    (selected : Nonempty (Derivation body Γ (programGraph (members (edge4 X W)) out
      (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (memberGraph vertices seed)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep len
  rw [graphRename]
  rw [unaryInputsRename] at len
  have g := renameInto guard j Δ keep
  rw [graphRename] at g
  have ss := renameInto selected j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at ss
  obtain ⟨atLen⟩ := exact_OpenMembersAtLength (edge4 X W) body β Δ (out.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨rule⟩ := roundSource paid (edge4 X W) body β Δ fuel (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (out.relabel j) (k.relabel j)
  obtain ⟨l⟩ := len
  obtain ⟨v⟩ := ss
  obtain ⟨g⟩ := g
  have run := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination atLen l)) v
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction run g)⟩

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

theorem recover (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (paid : ExactRetainedPredecessor) (ctx ty seed pool k : OTerm α)
    (selected : Nonempty (Derivation body Γ (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed])))
    (occurs : Nonempty (Derivation body Γ (memberGraph pool k))) :
    Nonempty (Derivation body Γ (occursInCover C s seed seed)) := by
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
  have source := atLength paid X W (ctx.relabel j) (ty.relabel j) vertices (seed.relabel j) (pool.relabel j) (k.relabel j) mm computed
  exact coverIntro C s (seed.relabel j) (seed.relabel j) vertices hv source

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginPoolProof
