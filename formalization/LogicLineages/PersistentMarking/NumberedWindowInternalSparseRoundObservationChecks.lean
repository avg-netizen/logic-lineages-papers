module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationInductionProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationChecks
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
open NumberedWindowInternalSparseRoundObservationTargets
open NumberedWindowInternalSparseRoundObservationInductionProof (allCounts)
open NumberedWindowInternalSparseRoundObservationSyntaxProof (applyAt sourceRename observedRename)
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

theorem exact_RoundObservation : ExactRoundObservation := by
  intro E M body α Γ i vertices ctx ty seed out k m dom cod arg
  let A := inputs E M i vertices ctx ty seed out k m dom cod arg
  obtain ⟨d⟩ := applyAt (body := body) (Delta := A :: Γ) E M i vertices ctx ty seed out k m dom cod arg
    (allCounts E M i) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

private theorem atLength (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (M : Program 5) (ctx ty seed m vertices pool dom cod arg value : OTerm α)
    (initial : Nonempty (Derivation body Γ (source (edge4 X W) M ctx ty dom cod arg seed value)))
    (hit : Nonempty (Derivation body Γ (memberGraph pool m)))
    (computed : Nonempty (Derivation body Γ (programGraph (members (edge4 X W)) pool (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (observed M ctx dom cod arg m value)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep length
  rw [observedRename]
  rw [unaryInputsRename] at length
  have start := renameInto initial j Δ keep
  rw [sourceRename] at start
  have g := renameInto hit j Δ keep
  rw [graphRename] at g
  have ss := renameInto computed j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at ss
  obtain ⟨atLen⟩ := exact_OpenMembersAtLength (edge4 X W) body β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨rule⟩ := exact_RoundObservation (edge4 X W) M body β Δ fuel (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) (pool.relabel j) (m.relabel j) (value.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
  obtain ⟨l⟩ := length
  obtain ⟨v⟩ := ss
  obtain ⟨g⟩ := g
  obtain ⟨start⟩ := start
  have run := Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination atLen l)) v
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction start (Derivation.conjunctionIntroduction run g))⟩

private theorem fromVertices (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (M : Program 5) (ctx ty seed m vertices dom cod arg value : OTerm α)
    (initial : Nonempty (Derivation body Γ (source (edge4 X W) M ctx ty dom cod arg seed value)))
    (least : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed m)))
    (physical : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed))) :
    Nonempty (Derivation body Γ (observed M ctx dom cod arg m value)) := by
  apply programCases (members (edge4 X W)) (membersTape vertices ctx ty seed) _
  intro β j Δ pool keep computed
  rw [observedRename]
  simp only [membersTape,quadInputsRename] at computed
  have v := renameInto physical j Δ keep
  rw [NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.unaryRename] at v
  have first := renameInto initial j Δ keep
  rw [sourceRename] at first
  have chosen := renameInto least j Δ keep
  rw [leastRename] at chosen
  let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
  let ys := membersTape (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨run⟩ := compositionValue (members (edge4 X W)) ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    pool xs ys computed (poolArgs C s xs (vertices.relabel j) v)
  obtain ⟨selection⟩ := exact_SelectedInSuppliedPool C X W s body β Δ (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) pool (m.relabel j)
  obtain ⟨chosen⟩ := chosen
  have hit := Derivation.implicationElimination selection (Derivation.conjunctionIntroduction run chosen)
  exact atLength C X W s M (ctx.relabel j) (ty.relabel j) (seed.relabel j) (m.relabel j)
    (vertices.relabel j) pool (dom.relabel j) (cod.relabel j) (arg.relabel j) (value.relabel j) first ⟨hit⟩ computed

theorem exact_SelectedObservation : ExactSelectedObservation := by
  intro C X W s M body α Γ ctx ty dom cod arg seed selected value
  let A := source (edge4 X W) M ctx ty dom cod arg seed value ⊓ leastGraph C X W s ctx ty seed selected
  have h : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have hs := Nonempty.intro (Derivation.conjunctionLeft h)
  have hl := Nonempty.intro (Derivation.conjunctionRight h)
  have result : Nonempty (Derivation body (A :: Γ) (observed M ctx dom cod arg selected value)) := by
    apply programCases (scratchVertices C s) ![seed] _
    intro β j Δ vertices keep physical
    rw [observedRename]
    rw [unaryInputsRename] at physical
    have src := renameInto hs j Δ keep
    rw [sourceRename] at src
    have least := renameInto hl j Δ keep
    rw [leastRename] at least
    exact fromVertices C X W s M _ _ _ _ vertices _ _ _ _ src least physical
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_RoundObservation
#print axioms exact_SelectedObservation
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationChecks
