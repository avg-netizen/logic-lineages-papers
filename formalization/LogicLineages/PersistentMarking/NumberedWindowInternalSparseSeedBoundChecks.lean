module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedBoundChecks (exact_OpenPackedLeastLowerBound)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed membersAtSeed)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparseSeedBoundTargets
open NumberedWindowInternalSparseSeedBoundInductionProof (seedRounds)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atLength (X : Program 2) (W : Program 3)
    (ctx ty vertices seed out : OTerm α)
    (guard : Nonempty (Derivation body Γ (memberGraph vertices seed)))
    (selected : Nonempty (Derivation body Γ (programGraph (members (edge4 X W)) out
      (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (memberGraph out seed)) := by
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
  obtain ⟨rule⟩ := seedRounds (edge4 X W) body β Δ (out.relabel j) fuel (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨l⟩ := len
  obtain ⟨v⟩ := ss
  obtain ⟨g⟩ := g
  have run := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination atLen l)) v
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction run g)⟩

theorem exact_SeedEveryRound : ExactSeedEveryRound := seedRounds

theorem exact_PackedSeedBound : ExactPackedSeedBound := by
  intro C X W s body α Γ ctx ty seed vertices minimum
  let tape := ![ctx,ty,seed]
  let A := leastGraph C X W s ctx ty seed minimum ⊓
    (programGraph (poolAtSeed C s) vertices tape ⊓ memberGraph vertices seed)
  let Δ := A :: Γ
  have given : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have inputs := Derivation.conjunctionRight given
  have result : Nonempty (Derivation body Δ (ltF seed minimum).not) := by
    apply programCases (membersAtSeed C X W s) tape _
    intro β j Θ pool keep computed
    simp only [tape,tripleInputsRename] at computed
    have cover := renameInto ⟨Derivation.conjunctionLeft inputs⟩ j Θ keep
    simp only [programRename,tape,tripleInputsRename] at cover
    have present := renameInto ⟨Derivation.conjunctionRight inputs⟩ j Θ keep
    rw [graphRename] at present
    have chosen := renameInto ⟨Derivation.conjunctionLeft given⟩ j Θ keep
    rw [leastRename] at chosen
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have selected := compositionRecover (members (edge4 X W))
      (![poolAtSeed C s,.projection 0,.projection 1,.projection 2] : Fin 4 → Program 3) pool xs
      (membersTape (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)) computed (by
        intro k
        refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
        · exact cover
        · exact projectionValue 0 xs
        · exact projectionValue 1 xs
        · obtain rfl := Fin.eq_zero c
          exact projectionValue 2 xs)
    obtain ⟨hit⟩ := atLength X W (ctx.relabel j) (ty.relabel j) (vertices.relabel j) (seed.relabel j) pool present selected
    obtain ⟨bounded⟩ := exact_OpenPackedLeastLowerBound C X W s body β Θ (ctx.relabel j) (ty.relabel j)
      (seed.relabel j) pool (seed.relabel j) (minimum.relabel j)
    obtain ⟨computed⟩ := computed
    obtain ⟨chosen⟩ := chosen
    change Nonempty (Derivation body Θ ((ltF seed minimum).relabel j).not)
    rw [orderRename]
    exact ⟨Derivation.implicationElimination bounded
      (Derivation.conjunctionIntroduction chosen (Derivation.conjunctionIntroduction computed hit))⟩
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_SeedEveryRound
#print axioms exact_PackedSeedBound
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundChecks
