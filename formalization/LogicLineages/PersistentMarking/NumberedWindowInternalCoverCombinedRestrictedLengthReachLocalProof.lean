module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachLocalProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRoundReachChecks (exact_RoundEdgeExtension)
open NumberedWindowInternalSparseSeedBoundChecks (exact_SeedEveryRound)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalCoverCombinedRestrictedLengthReachTargets

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

theorem exact_OpenCoverLengthReach : ExactOpenCoverLengthReach := by
  intro E body α Γ ctx ty vertices a b fuel pool length ma mb edge actual
  obtain ⟨l⟩ := length
  obtain ⟨selected⟩ := actual
  obtain ⟨law⟩ := exact_OpenMembersAtLength E body α Γ pool (suc fuel) vertices ctx ty a
  have finalRun : Nonempty (Derivation body Γ (roundGraph E pool (suc fuel) vertices ctx ty a)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination law l)) selected⟩
  apply programCases (rounds E) (roundsTape fuel vertices ctx ty a) _
  intro β j Δ before keep prior
  rw [roundsTapeRename] at prior
  rw [graphRename]
  have final' := renameInto finalRun j Δ keep
  rw [roundRename,sucRelabel] at final'
  have ma' := renameInto ma j Δ keep
  have mb' := renameInto mb j Δ keep
  rw [graphRename] at ma' mb'
  have edge' := renameInto edge j Δ keep
  rw [edgeRename] at edge'
  obtain ⟨origin⟩ := exact_SeedEveryRound E body β Δ before (fuel.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (a.relabel j)
  obtain ⟨step⟩ := exact_RoundEdgeExtension E body β Δ before (pool.relabel j) (fuel.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (a.relabel j) (a.relabel j) (b.relabel j)
  obtain ⟨prior⟩ := prior
  obtain ⟨final'⟩ := final'
  obtain ⟨ma'⟩ := ma'
  obtain ⟨mb'⟩ := mb'
  obtain ⟨edge'⟩ := edge'
  have present := Derivation.implicationElimination origin (Derivation.conjunctionIntroduction prior ma')
  exact ⟨Derivation.implicationElimination step (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction prior final')
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction present edge') mb'))⟩

#print axioms exact_OpenCoverLengthReach
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachLocalProof
