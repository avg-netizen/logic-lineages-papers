module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoChildReadIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoChildClosedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoReadInstallProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (headTransport programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans addSucc cancelSuc)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename addRelabel)
open ID1Completion.InternalRawListRecursionSyntaxProof (lookupGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (edgeRename)
open NumberedWindowInternalLiteralTypedContextMemoProof
open NumberedWindowInternalLiteralTypedDualMemoProof
open NumberedWindowInternalLiteralTypedMemoStageProof (carrierTerm childOnCarrier)
open NumberedWindowInternalLiteralTypedMemoChildClosedProof (typedPairRename memoCarrierRename memoBitRename)
open NumberedWindowInternalLiteralTypedMemoChildReadIntroProof (exact_OpenTypedMemoChildAtOffsets)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem contextTableRename {β : Type} (R : Program 4) (old ctx prev : OTerm α) (j : α → β) :
    (contextualTable R old ctx prev).relabel j = contextualTable R (old.relabel j) (ctx.relabel j) (prev.relabel j) := by
  simp only [contextualTable,programRename,tripleInputsRename,zRelabel]

theorem exact_OpenEarlierMemoOffset (key prev : OTerm α) (goal : Formula α)
    (below : D B Γ (ltF key (suc prev)))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (gap : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (OrdinaryArithmetic.addTerm (key.relabel j) gap) (prev.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply orderCases Γ key (suc prev) goal below
  intro β j Δ gap keeps relation
  rw [sucRelabel] at relation
  obtain ⟨bound⟩ := relation
  exact use β j Δ gap keeps ⟨cancelSuc (trans (symm (addSucc (key.relabel j) gap)) bound)⟩

private theorem lookupFromMemo (R : Program 4) (ctx old prev q r gap : OTerm α)
    (table : D B Γ (contextualTable R old ctx prev))
    (offset : D B Γ (eqn (OrdinaryArithmetic.addTerm (pairTerm q r) gap) prev))
    (bit : D B Γ (memoBit R ctx q r)) :
    D B Γ (lookupGraph (suc z) gap old) := by
  let k := pairTerm q r
  obtain ⟨e⟩ := offset
  have atKey : D B Γ (contextualTable R old ctx (OrdinaryArithmetic.addTerm k gap)) :=
    headTransport (scratchTable (constantZero 2) R) old prev
      (OrdinaryArithmetic.addTerm k gap) ![ctx,z] ⟨symm e⟩ table
  exact (exact_OpenContextMemoLookup R (suc z) ctx k gap old atKey).mpr
    ((exact_OpenSelectedContextMemo R (suc z) ctx q r).mp bit)

/-- The selected child's two actual positive memo rows produce an
accepted stage callback at any strictly earlier offsets in the very
same lexical table. No previously open graph is assumed to be true. -/
theorem exact_OpenChildMemoIntoStage (Base R : Program 4) (ctx old prev ty q r : OTerm α)
    (table : D B Γ (contextualTable R old ctx prev))
    (child : D B Γ (acceptEdge (dualContextMemo Base R) ctx ty q r))
    (fwd : D B Γ (ltF (pairTerm q r) (suc prev)))
    (rev : D B Γ (ltF (pairTerm r q) (suc prev))) :
    D B Γ (acceptEdge (childOnCarrier Base) (carrierTerm ctx old prev) ty q r) := by
  apply exact_OpenEarlierMemoOffset (pairTerm q r) prev _ fwd
  intro β j Δ f keep h
  rw [edgeRename,memoCarrierRename]
  rw [typedPairRename] at h
  have tb := renameInto table j Δ keep
  rw [contextTableRename] at tb
  have ch := renameInto child j Δ keep
  rw [edgeRename] at ch
  have b := renameInto rev j Δ keep
  rw [orderRename,typedPairRename,sucRelabel] at b
  let x := q.relabel j
  let y := r.relabel j
  let p := prev.relabel j
  let t := ty.relabel j
  let c := ctx.relabel j
  let old' := old.relabel j
  apply exact_OpenEarlierMemoOffset (pairTerm y x) p _ b
  intro γ n Θ g stay hn
  rw [edgeRename,memoCarrierRename]
  rw [typedPairRename] at hn
  have h' := renameInto h n Θ stay
  simp only [eqnRelabel,addRelabel,typedPairRename] at h'
  have tb' := renameInto tb n Θ stay
  rw [contextTableRename] at tb'
  have ch' := renameInto ch n Θ stay
  rw [edgeRename] at ch'
  let co := c.relabel n
  let pp := p.relabel n
  let tab := old'.relabel n
  let typ := t.relabel n
  let a := x.relabel n
  let z' := y.relabel n
  obtain ⟨base,l,r⟩ := (exact_OpenDualContextMemo Base R co typ a z').mp ch'
  have forward := lookupFromMemo R co tab pp a z' (f.relabel n) tb' h' l
  have reverse := lookupFromMemo R co tab pp z' a g tb' hn r
  exact exact_OpenTypedMemoChildAtOffsets Base co tab pp typ a z' (f.relabel n) g base h' hn forward reverse

#print axioms contextTableRename
#print axioms exact_OpenEarlierMemoOffset
#print axioms exact_OpenChildMemoIntoStage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoReadInstallProof
