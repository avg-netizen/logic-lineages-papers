module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumComparisonProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel suc z)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalLessThan (strictLess)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryMonotonicity (included)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparsePackedComparisonTargets (resultAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveList (u v k : OTerm α) (uv : Nonempty (Derivation body Γ (eqn u v)))
    (hit : Nonempty (Derivation body Γ (memberGraph u k))) : Nonempty (Derivation body Γ (memberGraph v k)) :=
  headTransport scratchMember (suc z) u v ![k] uv hit

private theorem equalIncluded (u v : OTerm α) (uv : Nonempty (Derivation body Γ (eqn u v))) :
    Nonempty (Derivation body Γ (included u v)) := by
  apply PrimaryMonotonicity.InclusionProof.introduce
  intro β j Θ k keep hit
  have e := renameInto uv j Θ keep
  rw [eqnRelabel] at e
  exact moveList (u.relabel j) (v.relabel j) k e hit

theorem compareAt (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3)
    (ctx ty a b va vb pa pb x y : OTerm α)
    (left : Derivation body Γ (resultAt C (guardedExchange C s baseX) W s ctx ty a va pa x))
    (right : Derivation body Γ (resultAt C (guardedExchange C s baseX) W s ctx ty b vb pb y))
    (arrow : Derivation body Γ (acceptEdge (edge4 (guardedExchange C s baseX) W) ctx ty a b)) :
    Nonempty (Derivation body Γ (strictLess y x).not) := by
  let X := guardedExchange C s baseX
  obtain ⟨cover⟩ := NumberedWindowInternalSparseCoverInstallationChecks.exact_GuardedEdgeCover
    C s baseX W body α Γ ctx ty a b va vb
  have equal := Derivation.implicationElimination cover (Derivation.conjunctionIntroduction arrow
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft left) (Derivation.conjunctionLeft right)))
  have r := Derivation.conjunctionRight right
  have l := Derivation.conjunctionRight left
  obtain ⟨ownB⟩ := NumberedWindowInternalSparsePackedSeedPresenceChecks.exact_SeedInGivenVertices
    C X W s body α Γ ctx ty b y vb
  have ub := Derivation.implicationElimination ownB (Derivation.conjunctionIntroduction
    (Derivation.conjunctionRight r) (Derivation.conjunctionLeft right))
  have toward := symm equal
  have atA := moveList vb va b ⟨toward⟩ ⟨ub⟩
  obtain ⟨destination⟩ := NumberedWindowInternalSparseCoverOccurrenceSyntaxProof.coverIntro C s a b va
    ⟨Derivation.conjunctionLeft left⟩ atA
  obtain ⟨ownA⟩ := NumberedWindowInternalSparsePackedSeedPresenceChecks.exact_SeedInGivenPool
    C X W s body α Γ ctx ty a x pa
  have ua := Derivation.implicationElimination ownA (Derivation.conjunctionIntroduction
    (Derivation.conjunctionRight l) (Derivation.conjunctionLeft l))
  obtain ⟨closure⟩ := NumberedWindowInternalSparseMinimumEdgeChecks.exact_PackedMembersClosure
    exact_RetainedPredecessor C X W s body α Γ ctx ty a pa a b
  have hit := Derivation.implicationElimination closure (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft l) ua)
    (Derivation.conjunctionIntroduction arrow destination))
  obtain ⟨inc⟩ := equalIncluded vb va ⟨toward⟩
  obtain ⟨order⟩ := NumberedWindowInternalSparsePackedComparisonChecks.exact_PackedSeedOrder
    exact_RetainedPredecessor C X W s body α Γ ctx ty b a vb va pb pa y x
  exact ⟨Derivation.implicationElimination order (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction right left) (Derivation.conjunctionIntroduction inc hit))⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumComparisonProof
