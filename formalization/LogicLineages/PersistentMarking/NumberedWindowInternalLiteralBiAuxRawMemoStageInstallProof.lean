module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoReadInstallProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeIntroProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoStageInstallProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
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
open NumberedWindowInternalLiteralTypedMemoReadInstallProof (exact_OpenChildMemoIntoStage)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The physical stage can read the two actual child indices of any
explicit scratch recursor. The acceptance of the caller stage is
separate from the identity of that recursor. -/
theorem exact_OpenInstallContextMemoStage (Base R : Program 4) (ctx old prev : OTerm α) (a b : AuxRow α)
    (parent : D B Γ (eqn (suc prev) (pairTerm a.term b.term)))
    (table : D B Γ (contextualTable R old ctx prev))
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (child : D B Γ (childAlternatives (dualContextMemo Base R) ctx a b)) :
    D B Γ (acceptEdge (stageGuard Base) (carrierTerm ctx old prev) z a.term b.term) := by
  let c := carrierTerm ctx old prev
  let M := childOnCarrier Base
  let E := dualContextMemo Base R
  let F := acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn ⊓ eqn a.arg b.arg
  let A := eqn a.fn b.fn ⊓ acceptEdge E ctx a.dom a.arg b.arg
  obtain ⟨⟨fwd⟩,⟨arg⟩⟩ := exact_OpenTypedAuxiliaryPairDecrease (B := B) (Γ := Γ) a b
  obtain ⟨⟨rev⟩,⟨argr⟩⟩ := exact_OpenAuxiliaryReverseChildKeys (B := B) (Γ := Γ) a b
  obtain ⟨key⟩ := parent
  obtain ⟨tab⟩ := table
  have one : D B (F :: Γ) (childAlternatives M c a b) := by
    have premise : Derivation B (F :: Γ) F := Derivation.hypothesis List.mem_cons_self
    obtain ⟨arc⟩ := exact_OpenChildMemoIntoStage Base R ctx old prev (rawCons a.dom a.cod) a.fn b.fn
      ⟨addHyp tab F⟩ ⟨Derivation.conjunctionLeft premise⟩
      ⟨orderRight (pairTerm a.fn b.fn) (symm (addHyp key F)) (addHyp fwd F)⟩
      ⟨orderRight (pairTerm b.fn a.fn) (symm (addHyp key F)) (addHyp rev F)⟩
    exact ⟨orLeft (Derivation.conjunctionIntroduction arc (Derivation.conjunctionRight premise))⟩
  have two : D B (A :: Γ) (childAlternatives M c a b) := by
    have premise : Derivation B (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
    obtain ⟨arc⟩ := exact_OpenChildMemoIntoStage Base R ctx old prev a.dom a.arg b.arg
      ⟨addHyp tab A⟩ ⟨Derivation.conjunctionRight premise⟩
      ⟨orderRight (pairTerm a.arg b.arg) (symm (addHyp key A)) (addHyp arg A)⟩
      ⟨orderRight (pairTerm b.arg a.arg) (symm (addHyp key A)) (addHyp argr A)⟩
    exact ⟨orRight (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft premise) arc)⟩
  obtain ⟨one⟩ := one
  obtain ⟨two⟩ := two
  obtain ⟨choice⟩ := child
  have stageChild : D B Γ (childAlternatives M c a b) :=
    ⟨disjunctionElimination choice (Derivation.implicationIntroduction one) (Derivation.implicationIntroduction two)⟩
  exact exact_OpenTypedAuxEdgeIntro (constantOne 4) M c z a b (oneConstantValue ![c,z,a.term,b.term])
    dom cod stageChild

#print axioms exact_OpenInstallContextMemoStage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoStageInstallProof
