module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserRawCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsParserReverseProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserPositiveCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc sucNeZeroApply)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldCellTargets (certifiedCell)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary certifiedCellRename)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (Preserves keepsComp)
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalOriginalRawConsParserReverseProof (exact_OriginalRawConsParserReverse)
open NumberedWindowInternalSparseParserRawCasesProof (exact_OriginalSparseParserRawCases)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An arbitrary original positive parser result is nil with empty scratch,
or a genuine cons with strictly smaller positively parsed raw tail and the
exact original scratch cons. The quantified goal and all surrounding proof
hypotheses are retained through the actual fresh witnesses. -/
theorem exact_OriginalPositiveSparseParserCases (n out : OTerm α) (goal : Formula α)
    (parsed : Report (B := B) (Γ := Γ) parser (suc out) ![n])
    (nilCase :
      Nonempty (Derivation B (eqn n z :: Γ) (eqn out z)) →
      Nonempty (Derivation B (eqn n z :: Γ) goal))
    (consCase : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (h t tailScratch : OTerm β),
      Preserves Γ j Δ →
      Nonempty (Derivation B Δ (certifiedCell (n.relabel j) h t)) →
      Nonempty (Derivation B Δ (consGraph (n.relabel j) h t)) →
      Nonempty (Derivation B Δ (eqn (n.relabel j) (rawCons h t))) →
      Nonempty (Derivation B Δ (ltF t (n.relabel j))) →
      Report (B := B) (Γ := Δ) parser (suc tailScratch) ![t] →
      Report (B := B) (Γ := Δ) consCode (out.relabel j) ![h,tailScratch] →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply exact_OriginalSparseParserRawCases n goal
  · intro nilReport
    obtain ⟨d⟩ := parsed
    have actual : Report (B := B) (Γ := eqn n z :: Γ) parser (suc out) ![n] :=
      ⟨addHyp d (eqn n z)⟩
    obtain ⟨equalOutputs⟩ := valueUnique parser (suc out) (suc z) ![n] actual nilReport
    exact nilCase ⟨cancelSuc equalOutputs⟩
  · intro β j Δ keep _ rejected
    have actual := renameParser n out parsed j Δ keep
    obtain ⟨impossible⟩ := valueUnique parser (suc (out.relabel j)) z ![n.relabel j] actual rejected
    exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩
  · intro β j Δ h t keep cell shape equalRaw bound
    have actual := renameParser n out parsed j Δ keep
    have literal : Report (B := B) (Γ := Δ) parser (suc (out.relabel j)) ![rawCons h t] :=
      moveUnary parser (suc (out.relabel j)) (n.relabel j) (rawCons h t) equalRaw actual
    apply exact_OriginalRawConsParserReverse h t (out.relabel j) (goal.relabel j) literal
    intro γ k Ξ suffix keep' parsedTail scratchCons _
    have movedCell := renameInto cell k Ξ keep'
    rw [certifiedCellRename] at movedCell
    have movedShape := renameInto shape k Ξ keep'
    rw [consGraphRename] at movedShape
    have movedEq := renameInto equalRaw k Ξ keep'
    rw [eqnRelabel,rawConsRename] at movedEq
    have movedBound := renameInto bound k Ξ keep'
    rw [orderRename] at movedBound
    have answer := consCase γ (k ∘ j) Ξ (h.relabel k) (t.relabel k) suffix
      (keepsComp Γ Δ Ξ j k keep keep')
      (by simpa only [Term.relabel_relabel] using movedCell)
      (by simpa only [Term.relabel_relabel] using movedShape)
      (by simpa only [Term.relabel_relabel] using movedEq)
      (by simpa only [Term.relabel_relabel] using movedBound)
      parsedTail
      (by simpa only [Term.relabel_relabel] using scratchCons)
    simpa only [formulaRelabelComposition] using answer

#print axioms exact_OriginalPositiveSparseParserCases

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserPositiveCasesProof
