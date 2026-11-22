module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastChecks
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
open NumberedWindowInternalSparseRoundLeastTargets
open NumberedWindowInternalSparseRoundLeastInductionProof (allCounts)
open NumberedWindowInternalSparseRoundLeastSyntaxProof (applyAt)
open NumberedWindowInternalSparseCoveredInstallationTargets (SameLeastOnEdge)
open NumberedWindowInternalSparseCoveredInstallationChecks (exact_CoveredEdgeValues)
open NumberedWindowInternalSparsePackedComparisonChecks (exact_SelectedInSuppliedPool)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)

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

theorem exact_RoundLeast : ExactRoundLeast := by
  intro C X W s paid body α Γ i vertices ctx ty seed out k m
  let A := inputs C X W s i vertices ctx ty seed out k m
  obtain ⟨d⟩ := applyAt (body := body) (Delta := A :: Γ) C X W s i vertices ctx ty seed out k m
    (allCounts C X W s paid i) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

private theorem atLength (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (ctx ty seed m vertices pool : OTerm α)
    (least : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed m)))
    (hit : Nonempty (Derivation body Γ (memberGraph pool m)))
    (computed : Nonempty (Derivation body Γ (programGraph (members (edge4 X W)) pool (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (leastGraph C X W s ctx ty m m)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep length
  rw [leastRename]
  rw [unaryInputsRename] at length
  have value := renameInto least j Δ keep
  rw [leastRename] at value
  have g := renameInto hit j Δ keep
  rw [graphRename] at g
  have ss := renameInto computed j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at ss
  obtain ⟨atLen⟩ := exact_OpenMembersAtLength (edge4 X W) body β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨rule⟩ := exact_RoundLeast C X W s paid body β Δ fuel (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) (pool.relabel j) (m.relabel j) (m.relabel j)
  obtain ⟨l⟩ := length
  obtain ⟨v⟩ := ss
  obtain ⟨g⟩ := g
  obtain ⟨value⟩ := value
  have run := Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination atLen l)) v
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction value (Derivation.conjunctionIntroduction run g))⟩

private theorem fromVertices (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (ctx ty seed m vertices : OTerm α)
    (least : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed m)))
    (physical : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed))) :
    Nonempty (Derivation body Γ (leastGraph C X W s ctx ty m m)) := by
  apply programCases (members (edge4 X W)) (membersTape vertices ctx ty seed) _
  intro β j Δ pool keep computed
  rw [leastRename]
  simp only [membersTape,quadInputsRename] at computed
  have v := renameInto physical j Δ keep
  rw [NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.unaryRename] at v
  have value := renameInto least j Δ keep
  rw [leastRename] at value
  let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
  let ys := membersTape (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨run⟩ := compositionValue (members (edge4 X W)) ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    pool xs ys computed (poolArgs C s xs (vertices.relabel j) v)
  obtain ⟨selection⟩ := exact_SelectedInSuppliedPool C X W s body β Δ (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) pool (m.relabel j)
  obtain ⟨value⟩ := value
  have hit := Derivation.implicationElimination selection (Derivation.conjunctionIntroduction run value)
  exact atLength C X W s paid (ctx.relabel j) (ty.relabel j) (seed.relabel j) (m.relabel j)
    (vertices.relabel j) pool ⟨value⟩ ⟨hit⟩ computed

theorem exact_CoveredLeastIdempotent : ExactCoveredLeastIdempotent := by
  intro C s baseX baseW body α Γ ctx ty seed m X W
  let A := leastGraph C X W s ctx ty seed m
  have value : Nonempty (Derivation body (A :: Γ) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result : Nonempty (Derivation body (A :: Γ) (leastGraph C X W s ctx ty m m)) := by
    apply programCases (scratchVertices C s) ![seed] _
    intro β j Δ vertices keep physical
    rw [leastRename]
    rw [unaryInputsRename] at physical
    have v := renameInto value j Δ keep
    simp only [A,leastRename] at v
    exact fromVertices C X W s (exact_CoveredEdgeValues C s baseX baseW) _ _ _ _ vertices v physical
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_RoundLeast
#print axioms exact_CoveredLeastIdempotent
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastChecks
