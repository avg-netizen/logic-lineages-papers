module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageClosureProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRecursiveLeastStabilityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveBooleanProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoUnfoldingProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans symm addSucc)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (edgeRename)
open NumberedWindowInternalLiteralPositiveBooleanProof (exact_OpenPositiveAuxShape)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (typedAuxEdgeGuard)
open NumberedWindowInternalLiteralTypedAuxEdgeIntroProof (exact_OpenTypedAuxEdgeNonAux)
open NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof (exact_OpenAuxShapeCases exact_OpenRetapePackedEdge auxRowRename)
open NumberedWindowInternalLiteralTypedAuxPairDecreaseProof (exact_OpenTypedAuxiliaryPairDecrease)
open NumberedWindowInternalLiteralTypedContextMemoProof
open NumberedWindowInternalLiteralTypedContextUpdateProof (exact_OpenContextMemoUpdate)
open NumberedWindowInternalLiteralTypedDualMemoProof
open NumberedWindowInternalLiteralTypedMemoStageProof
open NumberedWindowInternalLiteralTypedMemoStageClosureProof (exact_OpenTypedMemoUnrollStage)
open NumberedWindowInternalLiteralTypedMemoChildClosedProof (typedPairRename)
open NumberedWindowInternalLiteralTypedRecursiveClassesProof (TypedEdgeRefines)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def recursiveTypedMemo (Base : Program 4) : Program 4 := dualContextMemo Base (typedMemoStage Base)

private theorem fromPreceding (Base : Program 4) (ctx ty prev : OTerm α) (a b : AuxRow α)
    (parent : D B Γ (eqn (suc prev) (pairTerm a.term b.term)))
    (held : D B Γ (acceptEdge (recursiveTypedMemo Base) ctx ty a.term b.term)) :
    D B Γ (acceptEdge (typedAuxEdgeGuard Base (recursiveTypedMemo Base)) ctx ty a.term b.term) := by
  let R := typedMemoStage Base
  apply programCases (scratchTable (constantZero 2) R) ![prev,ctx,z] _
  intro β j Δ old stay table
  rw [edgeRename,auxRowRename,auxRowRename]
  simp only [tripleInputsRename,zRelabel] at table
  have selected := renameInto held j Δ stay
  rw [edgeRename,auxRowRename,auxRowRename] at selected
  have code := renameInto parent j Δ stay
  simp only [eqnRelabel,sucRelabel,typedPairRename,auxRowRename] at code
  let c := ctx.relabel j
  let t := ty.relabel j
  let p := prev.relabel j
  let l := a.map j
  let r := b.map j
  obtain ⟨onBase,memo,_⟩ := (exact_OpenDualContextMemo Base R c t l.term r.term).mp selected
  have actual := (exact_OpenSelectedContextMemo R (suc z) c l.term r.term).mp memo
  obtain ⟨eq⟩ := code
  have row : D B Δ (contextualRow R (suc z) c (suc p)) :=
    headTransport (scratchRow (constantZero 2) R) (suc z) (pairTerm l.term r.term) (suc p)
      ![c,z] ⟨symm eq⟩ actual
  have updated := (exact_OpenContextMemoUpdate R (suc z) c p old table).mpr row
  have accepted := (exact_OpenTypedMemoStage Base c old p l.term r.term ⟨eq⟩).mp updated
  exact exact_OpenTypedMemoUnrollStage Base c t old p l r ⟨eq⟩ table onBase accepted

theorem exact_OpenTypedMemoLiteralUnfolds (Base : Program 4) (ctx ty : OTerm α) (a b : AuxRow α)
    (held : D B Γ (acceptEdge (recursiveTypedMemo Base) ctx ty a.term b.term)) :
    D B Γ (acceptEdge (typedAuxEdgeGuard Base (recursiveTypedMemo Base)) ctx ty a.term b.term) := by
  have earlier := (exact_OpenTypedAuxiliaryPairDecrease (B := B) (Γ := Γ) a b).1
  apply orderCases Γ (pairTerm a.fn b.fn) (pairTerm a.term b.term) _ earlier
  intro β j Δ gap keep relation
  rw [edgeRename,auxRowRename,auxRowRename]
  simp only [typedPairRename,auxRowRename] at relation
  have active := renameInto held j Δ keep
  rw [edgeRename,auxRowRename,auxRowRename] at active
  let key := pairTerm (a.fn.relabel j) (b.fn.relabel j)
  obtain ⟨rel⟩ := relation
  exact fromPreceding Base (ctx.relabel j) (ty.relabel j) (OrdinaryArithmetic.addTerm key gap)
    (a.map j) (b.map j) ⟨trans (symm (addSucc key gap)) rel⟩ active

/-- A concrete finite memo program physically opens to the same
selected checker at smaller original raw child pairs. Numeric calibration
is a separate obligation; no evaluation theorem is used in this derivation. -/
theorem exact_OpenRecursiveTypedMemoUnfolds (Base : Program 4)
    (shape : Preserves Base (unaryObserver termShape)) :
    TypedEdgeRefines (recursiveTypedMemo Base) (typedAuxEdgeGuard Base (recursiveTypedMemo Base)) := by
  intro B α Γ ctx ty q r held
  let E := recursiveTypedMemo Base
  apply optionGraphCases termShape ![q] _
  · intro β j Δ keep zero
    rw [edgeRename]
    rw [unaryInputsRename] at zero
    have accepted := renameInto held j Δ keep
    rw [edgeRename] at accepted
    let c := ctx.relabel j
    let t := ty.relabel j
    let a := q.relabel j
    let b := r.relabel j
    have original := exact_OpenDualContextMemoBase Base (typedMemoStage Base) B β Δ c t a b accepted
    exact exact_OpenTypedAuxEdgeNonAux Base E c t a b original zero
  · intro β j Δ event keep positive
    rw [edgeRename]
    rw [unaryInputsRename] at positive
    have accepted := renameInto held j Δ keep
    rw [edgeRename] at accepted
    let c := ctx.relabel j
    let t := ty.relabel j
    let a := q.relabel j
    let b := r.relabel j
    have original := exact_OpenDualContextMemoBase Base (typedMemoStage Base) B β Δ c t a b accepted
    have src := exact_OpenPositiveAuxShape a event positive
    have dst := exact_OpenUnaryObserverElim termShape c t b (suc z)
      (shape B β Δ c t a b (suc z) original (exact_OpenUnaryObserverIntro termShape c t a (suc z) src))
    apply exact_OpenAuxShapeCases a _ src
    intro γ n Θ l stay left
    rw [edgeRename]
    have target := renameInto dst n Θ stay
    simp only [unaryRename,sucRelabel,zRelabel] at target
    have parent := renameInto accepted n Θ stay
    rw [edgeRename] at parent
    apply exact_OpenAuxShapeCases (b.relabel n) _ target
    intro η m Ξ r next right
    rw [edgeRename]
    have atLeft := renameInto left m Ξ next
    rw [eqnRelabel,auxRowRename] at atLeft
    have arrived := renameInto parent m Ξ next
    rw [edgeRename] at arrived
    let c' := (c.relabel n).relabel m
    let t' := (t.relabel n).relabel m
    let a' := (a.relabel n).relabel m
    let b' := (b.relabel n).relabel m
    let l' := l.map m
    have use := exact_OpenRetapePackedEdge E c' t' a' b' l'.term r.term atLeft right arrived
    have checked := exact_OpenTypedMemoLiteralUnfolds Base c' t' l' r use
    obtain ⟨he⟩ := atLeft
    obtain ⟨hf⟩ := right
    exact exact_OpenRetapePackedEdge (typedAuxEdgeGuard Base E) c' t' l'.term r.term a' b'
      ⟨symm he⟩ ⟨symm hf⟩ checked

#print axioms exact_OpenTypedMemoLiteralUnfolds
#print axioms exact_OpenRecursiveTypedMemoUnfolds
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoUnfoldingProof
