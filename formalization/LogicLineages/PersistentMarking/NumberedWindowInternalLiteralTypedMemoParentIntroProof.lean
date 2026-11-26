module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageInstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoUnfoldingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgesReversalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoParentIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans addSucc)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse edgeRename)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)
open NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof (auxRowRename)
open NumberedWindowInternalLiteralTypedAuxPairDecreaseProof (exact_OpenTypedAuxiliaryPairDecrease)
open NumberedWindowInternalLiteralTypedAuxEdgesReversalProof (exact_OpenReverseTypedChildCases)
open NumberedWindowInternalLiteralTypedContextMemoProof
open NumberedWindowInternalLiteralTypedContextUpdateProof
open NumberedWindowInternalLiteralTypedDualMemoProof
open NumberedWindowInternalLiteralTypedMemoStageProof
open NumberedWindowInternalLiteralTypedMemoChildClosedProof (typedPairRename memoBitRename)
open NumberedWindowInternalLiteralTypedMemoStageInstallProof (exact_OpenInstallTypedMemoStage)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem typedChildAlternativesRename {β : Type} (E : Program 4) (ctx : OTerm α) (a b : AuxRow α)
    (j : α → β) :
    (childAlternatives E ctx a b).relabel j = childAlternatives E (ctx.relabel j) (a.map j) (b.map j) := by
  change (((acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn).relabel j ⊓
    (eqn a.arg b.arg).relabel j) ⊔
    ((eqn a.fn b.fn).relabel j ⊓ (acceptEdge E ctx a.dom a.arg b.arg).relabel j)) = _
  rw [edgeRename,edgeRename,eqnRelabel,eqnRelabel,rawConsRename]
  rfl

private theorem parentAtPrev (Base : Program 4) (ctx prev : OTerm α) (a b : AuxRow α)
    (key : D B Γ (eqn (suc prev) (pairTerm a.term b.term)))
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (child : D B Γ (childAlternatives (recursiveTypedMemo Base) ctx a b)) :
    D B Γ (memoBit (typedMemoStage Base) ctx a.term b.term) := by
  let R := typedMemoStage Base
  apply programCases (scratchTable (constantZero 2) R) ![prev,ctx,z] _
  intro β j Δ old keep table
  rw [memoBitRename,auxRowRename,auxRowRename]
  simp only [tripleInputsRename,zRelabel] at table
  have k := renameInto key j Δ keep
  simp only [eqnRelabel,sucRelabel,typedPairRename,auxRowRename] at k
  have d := renameInto dom j Δ keep
  have e := renameInto cod j Δ keep
  simp only [eqnRelabel] at d e
  have arc := renameInto child j Δ keep
  rw [typedChildAlternativesRename] at arc
  let c := ctx.relabel j
  let p := prev.relabel j
  let l := a.map j
  let r := b.map j
  have openStage := exact_OpenInstallTypedMemoStage Base c old p l r k table d e arc
  have update := (exact_OpenTypedMemoStage Base c old p l.term r.term k).mpr openStage
  have row := (exact_OpenContextMemoUpdate R (suc z) c p old table).mp update
  have target : D B Δ (contextualRow R (suc z) c (pairTerm l.term r.term)) :=
    headTransport (scratchRow (constantZero 2) R) (suc z) (suc p) (pairTerm l.term r.term) ![c,z] k row
  exact (exact_OpenSelectedContextMemo R (suc z) c l.term r.term).mpr target

theorem exact_OpenTypedMemoParentBit (Base : Program 4) (ctx : OTerm α) (a b : AuxRow α)
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (child : D B Γ (childAlternatives (recursiveTypedMemo Base) ctx a b)) :
    D B Γ (memoBit (typedMemoStage Base) ctx a.term b.term) := by
  let k := pairTerm a.fn b.fn
  have below := (exact_OpenTypedAuxiliaryPairDecrease (B := B) (Γ := Γ) a b).1
  apply orderCases Γ k (pairTerm a.term b.term) _ below
  intro β j Δ gap keep bound
  rw [memoBitRename,auxRowRename,auxRowRename]
  simp only [k,typedPairRename,auxRowRename] at bound
  have d := renameInto dom j Δ keep
  have e := renameInto cod j Δ keep
  simp only [eqnRelabel] at d e
  have arc := renameInto child j Δ keep
  rw [typedChildAlternativesRename] at arc
  obtain ⟨eq⟩ := bound
  let oldK := pairTerm (a.fn.relabel j) (b.fn.relabel j)
  exact parentAtPrev Base (ctx.relabel j) (OrdinaryArithmetic.addTerm oldK gap) (a.map j) (b.map j)
    ⟨trans (symm (addSucc oldK gap)) eq⟩ d e arc

/-- The reverse direction of the concrete literal unfolding. Given
a genuine typed base parent and the actual smaller selected child,
both directional parent memo rows are derived from their own tables. -/
theorem exact_OpenTypedMemoAuxiliaryIntro (Base : Program 4) (reverse : CanReverse Base)
    (ctx ty : OTerm α) (a b : AuxRow α)
    (base : D B Γ (acceptEdge Base ctx ty a.term b.term))
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (child : D B Γ (childAlternatives (recursiveTypedMemo Base) ctx a b)) :
    D B Γ (acceptEdge (recursiveTypedMemo Base) ctx ty a.term b.term) := by
  let R := typedMemoStage Base
  have back := exact_OpenDualContextMemoReverse Base R reverse
  have reversed := exact_OpenReverseTypedChildCases (recursiveTypedMemo Base) back ctx a b dom cod child
  obtain ⟨eqD⟩ := dom
  obtain ⟨eqC⟩ := cod
  exact (exact_OpenDualContextMemo Base R ctx ty a.term b.term).mpr
    ⟨base,exact_OpenTypedMemoParentBit Base ctx a b ⟨eqD⟩ ⟨eqC⟩ child,
      exact_OpenTypedMemoParentBit Base ctx b a ⟨symm eqD⟩ ⟨symm eqC⟩ reversed⟩

#print axioms typedChildAlternativesRename
#print axioms exact_OpenTypedMemoParentBit
#print axioms exact_OpenTypedMemoAuxiliaryIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoParentIntroProof
