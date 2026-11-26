module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountBranchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountLeftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSwapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountEitherSideProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountLeftProof (exact_OpenProjectedCountLeft)
open NumberedWindowInternalProjectedCountInductionTargets (compared)
open NumberedWindowInternalProjectedCountInductionSyntaxProof (comparedRename appendedRename)
open NumberedWindowInternalLiteralCountAppendSwapProof (exact_LiteralAppendSwap)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)
open NumberedWindowInternalProjectedCountBranchTargets

theorem exact_ProjectedCountOnLeft : SideCountCongruence true :=
  exact_OpenProjectedCountLeft

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem advanceSwapped
    (key oldTail rt idle old retained tailJoin join swappedTail : OTerm α)
    (a : D B Γ (consGraph old key oldTail))
    (b : D B Γ (consGraph retained key rt))
    (after : D B Γ (appendGraph join idle retained))
    (beforeSwap : D B Γ (appendGraph swappedTail rt idle))
    (acceptTail : D B Γ (compared oldTail swappedTail)) :
    D B Γ (compared old join) := by
  apply programCases append ![retained,idle] (compared old join)
  intro β j Δ swapped keep swappedReport
  rw [binaryInputsRename] at swappedReport
  rw [comparedRename]
  have a' := renameInto a j Δ keep
  have b' := renameInto b j Δ keep
  rw [consGraphRename] at a' b'
  have after' := renameInto after j Δ keep
  have beforeSwap' := renameInto beforeSwap j Δ keep
  rw [appendedRename] at after' beforeSwap'
  have acceptTail' := renameInto acceptTail j Δ keep
  rw [comparedRename] at acceptTail'
  have extended := exact_OpenProjectedCountLeft B β Δ (key.relabel j) (oldTail.relabel j)
    (rt.relabel j) (idle.relabel j) (old.relabel j) (retained.relabel j) (swappedTail.relabel j)
    swapped a' b' beforeSwap' swappedReport acceptTail'
  exact exact_LiteralObserverTransitivity (old.relabel j) swapped (join.relabel j) extended
    (exact_LiteralAppendSwap (retained.relabel j) (idle.relabel j) swapped (join.relabel j)
      swappedReport after')

/-- Temporarily exchange the two actual append operands and use the checked
left cons law. Restore the original order by exact count commutation. -/
theorem exact_ProjectedCountOnRight : SideCountCongruence false := by
  intro B α Γ key oldTail rt idle old retained tailJoin joined original side pre post accepted
  apply programCases append ![rt,idle] (compared old joined)
  intro β j Δ swappedTail keep swappedReport
  rw [binaryInputsRename] at swappedReport
  rw [comparedRename]
  have pre' : D B Δ (appendGraph (tailJoin.relabel j) (idle.relabel j) (rt.relabel j)) := by
    have h : D B Γ (appendGraph tailJoin idle rt) := pre
    simpa only [appendedRename] using renameInto h j Δ keep
  have post' : D B Δ (appendGraph (joined.relabel j) (idle.relabel j) (retained.relabel j)) := by
    have h : D B Γ (appendGraph joined idle retained) := post
    simpa only [appendedRename] using renameInto h j Δ keep
  have a := renameInto original j Δ keep
  have b := renameInto side j Δ keep
  rw [consGraphRename] at a b
  have accepted' := renameInto accepted j Δ keep
  rw [comparedRename] at accepted'
  have moved := exact_LiteralObserverTransitivity (oldTail.relabel j) (tailJoin.relabel j)
    swappedTail accepted' (exact_LiteralAppendSwap (idle.relabel j) (rt.relabel j)
    (tailJoin.relabel j) swappedTail pre' swappedReport)
  exact advanceSwapped (key.relabel j) (oldTail.relabel j) (rt.relabel j) (idle.relabel j)
    (old.relabel j) (retained.relabel j) (tailJoin.relabel j) (joined.relabel j) swappedTail
    a b post' swappedReport moved

#print axioms exact_ProjectedCountOnLeft
#print axioms exact_ProjectedCountOnRight

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountEitherSideProof
