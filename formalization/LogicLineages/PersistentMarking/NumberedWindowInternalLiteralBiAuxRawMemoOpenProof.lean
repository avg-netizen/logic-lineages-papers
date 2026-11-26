module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoStageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoStageInstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoParentIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue headTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans symm addSucc)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof (auxRowRename)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)
open NumberedWindowInternalLiteralTypedAuxPairDecreaseProof (exact_OpenTypedAuxiliaryPairDecrease)
open NumberedWindowInternalLiteralTypedContextMemoProof
open NumberedWindowInternalLiteralTypedContextUpdateProof
open NumberedWindowInternalLiteralTypedDualMemoProof
open NumberedWindowInternalLiteralTypedMemoChildClosedProof (typedPairRename memoBitRename)
open NumberedWindowInternalLiteralTypedMemoParentIntroProof (typedChildAlternativesRename)
open NumberedWindowInternalLiteralBiAuxRawMemoStageProof
open NumberedWindowInternalLiteralBiAuxRawMemoStageInstallProof (exact_OpenInstallContextMemoStage)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def biAuxRawMemo (X : Program 2) (V : Program 1) : Program 2 :=
  .composition (selectedContextMemo (rawAuxMemoStage X V)) ![constantZero 2,.projection 0,.projection 1]

theorem exact_OpenBiAuxRawMemoSelected (X : Program 2) (V : Program 1) (q r : OTerm α) :
    D B Γ (programGraph (biAuxRawMemo X V) (suc z) ![q,r]) ↔
      D B Γ (memoBit (rawAuxMemoStage X V) z q r) := by
  let R := rawAuxMemoStage X V
  let ps : Fin 3 → Program 2 := ![constantZero 2,.projection 0,.projection 1]
  let xs : Fin 2 → OTerm α := ![q,r]
  let ys : Fin 3 → OTerm α := ![z,q,r]
  have reports : ∀ i, D B Γ (programGraph (ps i) (ys i) xs) := fun i =>
    Fin.cases (zeroConstantValue xs)
      (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j))) i
  exact ⟨fun h => compositionRecover (selectedContextMemo R) ps (suc z) xs ys h reports,
    fun h => compositionValue (selectedContextMemo R) ps (suc z) xs ys h reports⟩

private theorem parentAtPrev (X : Program 2) (V : Program 1) (prev : OTerm α) (a b : AuxRow α)
    (key : D B Γ (eqn (suc prev) (pairTerm a.term b.term)))
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (liveA : D B Γ (unary V (suc z) a.term)) (liveB : D B Γ (unary V (suc z) b.term))
    (child : D B Γ (childAlternatives (dualContextMemo (constantOne 4) (rawAuxMemoStage X V)) z a b)) :
    D B Γ (memoBit (rawAuxMemoStage X V) z a.term b.term) := by
  let R := rawAuxMemoStage X V
  apply programCases (scratchTable (constantZero 2) R) ![prev,z,z] _
  intro β j Δ old keep table
  rw [memoBitRename,auxRowRename,auxRowRename,zRelabel]
  simp only [tripleInputsRename,zRelabel] at table
  have k := renameInto key j Δ keep
  simp only [eqnRelabel,sucRelabel,typedPairRename,auxRowRename] at k
  have d := renameInto dom j Δ keep
  have e := renameInto cod j Δ keep
  simp only [eqnRelabel] at d e
  have va := renameInto liveA j Δ keep
  have vb := renameInto liveB j Δ keep
  simp only [unaryRename,auxRowRename,sucRelabel,zRelabel] at va vb
  have arc := renameInto child j Δ keep
  rw [typedChildAlternativesRename,zRelabel] at arc
  let p := prev.relabel j
  let l := a.map j
  let r := b.map j
  have stage := exact_OpenInstallContextMemoStage (constantOne 4) R z old p l r k table d e arc
  have shape : D B Δ (unary NumberedWindowInternalSparseRawFunctionFrame.termShape (suc z) l.term) :=
    (termReports (body := B) (Γ := Δ) l.dom l.cod l.fn l.arg).1
  have update := exact_OpenBiAuxRawMemoStage X V old p l.term r.term k shape va vb stage
  have row := (exact_OpenContextMemoUpdate R (suc z) z p old table).mp update
  have final : D B Δ (contextualRow R (suc z) z (pairTerm l.term r.term)) :=
    headTransport (scratchRow (constantZero 2) R) (suc z) (suc p) (pairTerm l.term r.term) ![z,z] k row
  exact (exact_OpenSelectedContextMemo R (suc z) z l.term r.term).mpr final

theorem exact_OpenBiAuxRawParentMemo (X : Program 2) (V : Program 1) (a b : AuxRow α)
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (liveA : D B Γ (unary V (suc z) a.term)) (liveB : D B Γ (unary V (suc z) b.term))
    (child : D B Γ (childAlternatives (dualContextMemo (constantOne 4) (rawAuxMemoStage X V)) z a b)) :
    D B Γ (memoBit (rawAuxMemoStage X V) z a.term b.term) := by
  let k := pairTerm a.fn b.fn
  have earlier := (exact_OpenTypedAuxiliaryPairDecrease (B := B) (Γ := Γ) a b).1
  apply orderCases Γ k (pairTerm a.term b.term) _ earlier
  intro β j Δ gap keep bound
  rw [memoBitRename,auxRowRename,auxRowRename,zRelabel]
  simp only [k,typedPairRename,auxRowRename] at bound
  have d := renameInto dom j Δ keep
  have e := renameInto cod j Δ keep
  simp only [eqnRelabel] at d e
  have va := renameInto liveA j Δ keep
  have vb := renameInto liveB j Δ keep
  simp only [unaryRename,auxRowRename,sucRelabel,zRelabel] at va vb
  have arc := renameInto child j Δ keep
  rw [typedChildAlternativesRename,zRelabel] at arc
  obtain ⟨rel⟩ := bound
  let old := pairTerm (a.fn.relabel j) (b.fn.relabel j)
  exact parentAtPrev X V (OrdinaryArithmetic.addTerm old gap) (a.map j) (b.map j)
    ⟨trans (symm (addSucc old gap)) rel⟩ d e va vb arc

#print axioms exact_OpenBiAuxRawMemoSelected
#print axioms exact_OpenBiAuxRawParentMemo
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoOpenProof
