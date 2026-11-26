module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (coords coordsRename)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveChosenConsChecks (exact_OpenFinishCons)
open NumberedWindowInternalSparsePositiveChosenConsTargets (genuineHead)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph)
open NumberedWindowInternalSparsePositiveDeadCurrentChecks (exact_OpenNoCurrentFinishZero)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (finishAtRename)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePositiveWindowTargets
open NumberedWindowInternalLiteralOpenMatchedMotiveProof
open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalLiteralOpenMatchedAdvanceLawProof (MatchedAdvanceAt resultOrPath)
open NumberedWindowInternalLiteralOpenMatchedReportProof (pulled)
open NumberedWindowInternalLiteralOpenMatchedBindingProof (pulledRename)
open ID1Completion.InternalQuotientComparisonProof (orRight)
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tailAt (raw : Program 5) (least : Program 3) (ctx ty source cert target h t n : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert h t)))
    (whole : Nonempty (Derivation body Γ (finishAt raw least ctx ty source cert target)))
    (next : Nonempty (Derivation body Γ (selectedGraph raw least n ctx ty (suc source) h))) :
    Nonempty (Derivation body Γ (finishGraph raw least (suc target) ctx ty n t)) := by
  obtain ⟨c⟩ := cell
  obtain ⟨a⟩ := next
  have head : Nonempty (Derivation body Γ (genuineHead raw least ctx ty (suc source) cert h t n)) :=
    ⟨Derivation.conjunctionIntroduction c a⟩
  obtain ⟨rule⟩ := closedApply (exact_OpenFinishCons body raw least α (suc target) ctx ty (suc source) cert h t n) head
  obtain ⟨f⟩ := whole
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft rule) f⟩


theorem fromCons (K : MatchContext) (L : Program 3) (raw : Program 5)
    (law : MatchedAdvanceAt K L raw) (ctx dom cod arg fn cert target value hd tl : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (domain : Derivation body Γ (typedFormation K ctx dom cod arg))
    (whole : Derivation body Γ (finishAt raw (L) ctx (rawCons dom cod) fn cert target))
    (found : Derivation body Γ (reported L ctx cod (auxiliaryTerm dom cod target arg) value))
    (hyp : Nonempty (Derivation body Γ (safe K L raw ctx dom cod arg tl target value))) :
    Nonempty (Derivation body Γ (pulled L raw ctx cod (auxiliaryTerm dom cod fn arg) value)) := by
  let least := L
  let ty := rawCons dom cod
  apply optionGraphCases (advance raw least) (coords ctx ty (suc fn) hd) _
  · intro β j Δ keep absent
    rw [coordsRename,sucRelabel] at absent
    have c := renameInto cell j Δ keep
    rw [consGraphRename] at c
    have f := renameInto ⟨whole⟩ j Δ keep
    rw [finishAtRename] at f
    have rest := tailAt raw least _ _ _ _ _ _ _ z c f absent
    obtain ⟨dead⟩ := exact_OpenNoCurrentFinishZero body raw least β (ctx.relabel j) (ty.relabel j) (tl.relabel j)
    obtain ⟨eq⟩ := valueUnique (finish raw least) (suc (target.relabel j)) z
      (args4 (ctx.relabel j) (ty.relabel j) z (tl.relabel j)) rest ⟨weakenClosed dead Δ⟩
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  · intro β j Δ next keep accepted
    rw [pulledRename,auxiliaryRename]
    rw [coordsRename,sucRelabel] at accepted
    have c := renameInto cell j Δ keep
    rw [consGraphRename] at c
    have f := renameInto ⟨whole⟩ j Δ keep
    rw [finishAtRename] at f
    obtain ⟨rest⟩ := tailAt raw least _ _ _ _ _ _ _ (suc next) c f accepted
    have old := renameInto hyp j Δ keep
    rw [safeRename] at old
    have form := renameInto ⟨domain⟩ j Δ keep
    rw [typedFormationRename] at form
    have atEnd := renameInto ⟨found⟩ j Δ keep
    rw [reportedRename,auxiliaryRename] at atEnd
    obtain ⟨old⟩ := old
    obtain ⟨form⟩ := form
    obtain ⟨atEnd⟩ := atEnd
    obtain ⟨ih⟩ := applyAt K L raw (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
      (tl.relabel j) (target.relabel j) (value.relabel j) next old
    change Derivation body Δ (finishAt raw least _ ((rawCons dom cod).relabel j) next _ _) at rest
    rw [rawConsRename] at rest
    have suffix := Derivation.implicationElimination ih
      (Derivation.conjunctionIntroduction form (Derivation.conjunctionIntroduction rest atEnd))
    obtain ⟨accepted⟩ := accepted
    simp only [ty,rawConsRename] at accepted
    obtain ⟨move⟩ := law body β Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
      (fn.relabel j) next (hd.relabel j) (value.relabel j)
    exact ⟨Derivation.implicationElimination move
      (Derivation.conjunctionIntroduction form (Derivation.conjunctionIntroduction accepted suffix))⟩

#print axioms fromCons
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedConsProof
