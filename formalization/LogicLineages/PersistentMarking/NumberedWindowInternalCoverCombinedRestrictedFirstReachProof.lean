module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachLocalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverCombinedRestrictedFirstReachLocalProof (fromActualFirstRounds)
open NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets

attribute [local irreducible] programGraph

private theorem edgeRename {α β : Type} (E : Program 4) (ctx ty a b : OTerm α) (j : α → β) :
    (acceptEdge E ctx ty a b).relabel j = acceptEdge E (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [acceptEdge,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

private theorem roundsTapeRename {α β : Type} (fuel vertices ctx ty seed : OTerm α) (j : α → β) :
    (fun i => (roundsTape fuel vertices ctx ty seed i).relabel j) =
      roundsTape (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun u => Fin.elim0 u) d) c) b) a) i <;> rfl

private theorem chooseRound {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (E : Program 4) (fuel vertices ctx ty seed : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (roundGraph E out (fuel.relabel j) (vertices.relabel j)
        (ctx.relabel j) (ty.relabel j) (seed.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases (rounds E) (roundsTape fuel vertices ctx ty seed) goal
  intro β j Δ out keep observed
  rw [roundsTapeRename] at observed
  exact k β j Δ out keep observed

theorem exact_OpenCoverFirstReach : ExactOpenCoverFirstReach := by
  intro E body α Γ ctx ty vertices a b goal ma mb edge k
  apply chooseRound E z vertices ctx ty a goal
  intro β i Δ before keep0 zeroRun
  rw [zRelabel] at zeroRun
  have ma' := renameInto ma i Δ keep0
  have mb' := renameInto mb i Δ keep0
  have edge' := renameInto edge i Δ keep0
  rw [graphRename] at ma' mb'
  rw [edgeRename] at edge'
  apply chooseRound E (suc z) (vertices.relabel i) (ctx.relabel i) (ty.relabel i) (a.relabel i) (goal.relabel i)
  intro γ j Θ after keep1 oneRun
  simp only [sucRelabel,zRelabel] at oneRun
  have zero' := renameInto zeroRun j Θ keep1
  simp only [roundRename,zRelabel] at zero'
  have ma'' := renameInto ma' j Θ keep1
  have mb'' := renameInto mb' j Θ keep1
  have edge'' := renameInto edge' j Θ keep1
  rw [graphRename] at ma'' mb''
  rw [edgeRename] at edge''
  have facts := fromActualFirstRounds E ((ctx.relabel i).relabel j) ((ty.relabel i).relabel j)
    ((vertices.relabel i).relabel j) ((a.relabel i).relabel j) ((b.relabel i).relabel j)
    (before.relabel j) after ma'' mb'' edge'' zero' oneRun
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel (j ∘ i) ∈ Θ := by
    rw [← formulaRelabelComposition]
    exact keep1 _ (keep0 p hp)
  rw [formulaRelabelComposition]
  exact k γ (j ∘ i) Θ (before.relabel j) after keep (by
    simpa only [Term.relabel_relabel] using facts)

#print axioms exact_OpenCoverFirstReach
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachProof
