module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeReversalProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralEnrichedEdgeProof
open NumberedWindowInternalLiteralRoundObserverTargets (observe)
open NumberedWindowInternalLiteralRoundObserverSyntaxProof (observeRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)

attribute [local irreducible] programGraph

def CanReverse (E : Program 4) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b : OTerm α),
    D B Γ (acceptEdge E ctx ty a b) → D B Γ (acceptEdge E ctx ty b a)

theorem edgeRename {α β : Type} (E : Program 4) (ctx ty a b : OTerm α) (j : α → β) :
    (acceptEdge E ctx ty a b).relabel j =
      acceptEdge E (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [acceptEdge,edgeTape,programRename,quadInputsRename,sucRelabel,zRelabel]

/-- Reversing the physically enriched edge does not introduce a new
equality premise. A real observer read on one end is transported over
the original direction and used twice in the reversed report. -/
theorem exact_OpenEnrichedEdgeReverses (E : Program 4) (O : Program 3)
    (baseReverse : CanReverse E) : CanReverse (enrichedEdge E O) := by
  intro B α Γ ctx ty a b forward
  apply programCases O ![ctx,ty,a] (acceptEdge (enrichedEdge E O) ctx ty b a)
  intro β j Δ value keep left
  rw [edgeRename]
  rw [tripleInputsRename] at left
  have h := renameInto forward j Δ keep
  rw [edgeRename] at h
  let c := ctx.relabel j
  let t := ty.relabel j
  let u := a.relabel j
  let v := b.relabel j
  have old := exact_OpenEnrichedEdgeBase E O c t u v h
  have reverse := baseReverse B β Δ c t u v old
  have right := exact_OpenEnrichedEdgeObservation E O B β Δ c t u v value h left
  exact exact_OpenEnrichedEdgeIntro E O c t v u value value reverse right left ⟨refl value⟩

#print axioms exact_OpenEnrichedEdgeReverses
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeReversalProof
