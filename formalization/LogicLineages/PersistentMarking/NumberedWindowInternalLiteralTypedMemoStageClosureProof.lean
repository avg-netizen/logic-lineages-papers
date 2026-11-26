module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoChildClosedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeIntroProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageClosureProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open ID1Completion.InternalLessThan (constantOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives exact_OpenTypedAuxEdgeRows)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (typedAuxEdgeGuard)
open NumberedWindowInternalLiteralTypedAuxEdgeIntroProof (exact_OpenTypedAuxEdgeIntro)
open NumberedWindowInternalLiteralTypedAuxPairDecreaseProof (exact_OpenTypedAuxiliaryPairDecrease)
open NumberedWindowInternalLiteralTypedAuxReverseKeyProof (exact_OpenAuxiliaryReverseChildKeys)
open NumberedWindowInternalLiteralTypedContextMemoProof (contextualTable)
open NumberedWindowInternalLiteralTypedDualMemoProof (dualContextMemo)
open NumberedWindowInternalLiteralTypedMemoStageProof
open NumberedWindowInternalLiteralTypedMemoChildClosedProof (exact_OpenTypedMemoChildClosed)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenTypedMemoUnrollStage (Base : Program 4) (ctx ty old prev : OTerm α) (a b : AuxRow α)
    (parent : D B Γ (eqn (suc prev) (pairTerm a.term b.term)))
    (table : D B Γ (contextualTable (typedMemoStage Base) old ctx prev))
    (onBase : D B Γ (acceptEdge Base ctx ty a.term b.term))
    (stage : D B Γ (acceptEdge (stageGuard Base) (carrierTerm ctx old prev) z a.term b.term)) :
    D B Γ (acceptEdge (typedAuxEdgeGuard Base (dualContextMemo Base (typedMemoStage Base)))
      ctx ty a.term b.term) := by
  let c := carrierTerm ctx old prev
  let M := childOnCarrier Base
  let R := typedMemoStage Base
  let E := dualContextMemo Base R
  let F := acceptEdge M c (rawCons a.dom a.cod) a.fn b.fn ⊓ eqn a.arg b.arg
  let A := eqn a.fn b.fn ⊓ acceptEdge M c a.dom a.arg b.arg
  obtain ⟨all⟩ := exact_OpenTypedAuxEdgeRows (constantOne 4) M c z a b stage
  obtain ⟨⟨fwd⟩, ⟨arg⟩⟩ := exact_OpenTypedAuxiliaryPairDecrease (B := B) (Γ := Γ) a b
  obtain ⟨⟨rev⟩, ⟨argr⟩⟩ := exact_OpenAuxiliaryReverseChildKeys (B := B) (Γ := Γ) a b
  obtain ⟨key⟩ := parent
  obtain ⟨tab⟩ := table
  have one : D B (F :: Γ) (childAlternatives E ctx a b) := by
    have premise : Derivation B (F :: Γ) F := Derivation.hypothesis List.mem_cons_self
    obtain ⟨arc⟩ := exact_OpenTypedMemoChildClosed Base R ctx old prev (rawCons a.dom a.cod) a.fn b.fn
      ⟨addHyp tab F⟩ ⟨Derivation.conjunctionLeft premise⟩
      ⟨orderRight (pairTerm a.fn b.fn) (symm (addHyp key F)) (addHyp fwd F)⟩
      ⟨orderRight (pairTerm b.fn a.fn) (symm (addHyp key F)) (addHyp rev F)⟩
    exact ⟨orLeft (Derivation.conjunctionIntroduction arc (Derivation.conjunctionRight premise))⟩
  have two : D B (A :: Γ) (childAlternatives E ctx a b) := by
    have premise : Derivation B (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
    obtain ⟨arc⟩ := exact_OpenTypedMemoChildClosed Base R ctx old prev a.dom a.arg b.arg
      ⟨addHyp tab A⟩ ⟨Derivation.conjunctionRight premise⟩
      ⟨orderRight (pairTerm a.arg b.arg) (symm (addHyp key A)) (addHyp arg A)⟩
      ⟨orderRight (pairTerm b.arg a.arg) (symm (addHyp key A)) (addHyp argr A)⟩
    exact ⟨orRight (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft premise) arc)⟩
  obtain ⟨one⟩ := one
  obtain ⟨two⟩ := two
  have child : D B Γ (childAlternatives E ctx a b) :=
    ⟨disjunctionElimination (Derivation.conjunctionRight (Derivation.conjunctionRight all))
      (Derivation.implicationIntroduction one) (Derivation.implicationIntroduction two)⟩
  exact exact_OpenTypedAuxEdgeIntro Base E ctx ty a b onBase ⟨Derivation.conjunctionLeft all⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight all)⟩ child

#print axioms exact_OpenTypedMemoUnrollStage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageClosureProof
