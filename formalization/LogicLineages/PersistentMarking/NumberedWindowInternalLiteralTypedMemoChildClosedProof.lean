module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoChildReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxReverseKeyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoChildClosedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans symm cancelSuc addSucc)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (edgeRename)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedContextMemoProof
open NumberedWindowInternalLiteralTypedDualMemoProof
open NumberedWindowInternalLiteralTypedMemoStageProof
open NumberedWindowInternalLiteralTypedMemoChildReportProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem typedPairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (pairTerm a b).relabel j = pairTerm (a.relabel j) (b.relabel j) := by
  simp only [pairTerm,addRelabel,mulRelabel]

theorem memoCarrierRename {β : Type} (ctx old prev : OTerm α) (j : α → β) :
    (carrierTerm ctx old prev).relabel j = carrierTerm (ctx.relabel j) (old.relabel j) (prev.relabel j) := by
  simp only [carrierTerm,rawConsRename,zRelabel]

theorem memoBitRename {β : Type} (R : Program 4) (ctx q r : OTerm α) (j : α → β) :
    (memoBit R ctx q r).relabel j = memoBit R (ctx.relabel j) (q.relabel j) (r.relabel j) := by
  simp only [memoBit,programRename,tripleInputsRename,sucRelabel,zRelabel]

private def orient (swap : Bool) (q r : OTerm α) : OTerm α := if swap then r else q

private theorem childRow (Base R : Program 4) (swap : Bool) (ctx old prev ty q r : OTerm α)
    (tab : D B Γ (contextualTable R old ctx prev))
    (read : D B Γ (acceptEdge (childOnCarrier Base) (carrierTerm ctx old prev) ty q r))
    (earlier : D B Γ (ltF (pairTerm (orient swap q r) (orient swap r q)) (suc prev))) :
    D B Γ (memoBit R ctx (orient swap q r) (orient swap r q)) := by
  apply orderCases Γ _ (suc prev) _ earlier
  intro β j Δ gap keep offset
  rw [memoBitRename]
  simp only [typedPairRename,sucRelabel] at offset
  have table := renameInto tab j Δ keep
  simp only [contextualTable,programRename,tripleInputsRename,zRelabel] at table
  have report := renameInto read j Δ keep
  rw [edgeRename,memoCarrierRename] at report
  let c := ctx.relabel j
  let t := old.relabel j
  let p := prev.relabel j
  let a := (orient swap q r).relabel j
  let b := (orient swap r q).relabel j
  let key := pairTerm a b
  obtain ⟨known⟩ := offset
  have gapEq : D B Δ (eqn (OrdinaryArithmetic.addTerm key gap) p) :=
    ⟨cancelSuc (trans (symm (addSucc key gap)) known)⟩
  have atKey : D B Δ (contextualTable R t c (OrdinaryArithmetic.addTerm key gap)) :=
    headTransport (scratchTable (ID1Completion.InternalAcceptance.constantZero 2) R) t p
      (OrdinaryArithmetic.addTerm key gap) ![c,z] (by exact ⟨symm (Classical.choice gapEq)⟩) table
  have reads := exact_OpenTypedMemoChildReads Base c t p (ty.relabel j) (q.relabel j) (r.relabel j) report
  have parsed : D B Δ (ID1Completion.InternalRawListRecursionSyntaxProof.lookupGraph (suc z) gap t) := by
    cases swap
    · exact reads.1 gap gapEq
    · exact reads.2 gap gapEq
  exact (exact_OpenSelectedContextMemo R (suc z) c a b).mpr
    ((exact_OpenContextMemoLookup R (suc z) c key gap t atKey).mp parsed)

/-- A physically accepted child alternative in a memo update yields the same
edge program at that child. Both directional lookups are read out of the
actual earlier table, under the identical lexical context. -/
theorem exact_OpenTypedMemoChildClosed (Base R : Program 4) (ctx old prev ty q r : OTerm α)
    (tab : D B Γ (contextualTable R old ctx prev))
    (read : D B Γ (acceptEdge (childOnCarrier Base) (carrierTerm ctx old prev) ty q r))
    (forward : D B Γ (ltF (pairTerm q r) (suc prev)))
    (reverse : D B Γ (ltF (pairTerm r q) (suc prev))) :
    D B Γ (acceptEdge (dualContextMemo Base R) ctx ty q r) :=
  (exact_OpenDualContextMemo Base R ctx ty q r).mpr
    ⟨exact_OpenTypedMemoBaseReport Base ctx old prev ty q r read,
      childRow Base R false ctx old prev ty q r tab read forward,
      childRow Base R true ctx old prev ty q r tab read reverse⟩

#print axioms typedPairRename
#print axioms memoCarrierRename
#print axioms memoBitRename
#print axioms exact_OpenTypedMemoChildClosed
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoChildClosedProof
