module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainMemberProof

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed poolAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseSeedBoundChecks (exact_SeedEveryRound)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}


private theorem seedInMembers (E : Program 4) (vertices ctx ty seed pool : OTerm α)
    (present : Nonempty (Derivation body Γ (memberGraph vertices seed)))
    (computed : Nonempty (Derivation body Γ (programGraph (members E) pool
      (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (memberGraph pool seed)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep length
  rw [graphRename]
  rw [unaryInputsRename] at length
  have hit := renameInto present j Δ keep
  rw [graphRename] at hit
  have selected := renameInto computed j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at selected
  obtain ⟨length⟩ := length
  obtain ⟨hit⟩ := hit
  obtain ⟨selected⟩ := selected
  obtain ⟨atLength⟩ := exact_OpenMembersAtLength E body β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  have round := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination atLength length)) selected
  obtain ⟨keepSeed⟩ := exact_SeedEveryRound E body β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  exact ⟨Derivation.implicationElimination keepSeed (Derivation.conjunctionIntroduction round hit)⟩

private theorem actualMembers (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed vertices pool : OTerm α)
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed)))
    (packed : Nonempty (Derivation body Γ (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed]))) :
    Nonempty (Derivation body Γ (programGraph (members (edge4 X W)) pool
      (membersTape vertices ctx ty seed))) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  apply compositionRecover (members (edge4 X W))
    ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    pool xs (membersTape vertices ctx ty seed) packed
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2)
      vertices xs ![seed] cover
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero l
    exact projectionValue 2 xs

theorem seedInComputedPool : ExactSeedInComputedPool := by
  intro C X W s body α Γ ctx ty seed vertices pool
  let data := unary (scratchVertices C s) vertices seed ⊓
    programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed]
  let Δ := (data ⊓ memberGraph vertices seed) :: Γ
  have h : Derivation body Δ (data ⊓ memberGraph vertices seed) := Derivation.hypothesis List.mem_cons_self
  let calls := Derivation.conjunctionLeft h
  have actual := actualMembers C X W s ctx ty seed vertices pool
    ⟨Derivation.conjunctionLeft calls⟩ ⟨Derivation.conjunctionRight calls⟩
  obtain ⟨hit⟩ := seedInMembers (edge4 X W) vertices ctx ty seed pool ⟨Derivation.conjunctionRight h⟩ actual
  exact ⟨Derivation.implicationIntroduction hit⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainMemberProof
