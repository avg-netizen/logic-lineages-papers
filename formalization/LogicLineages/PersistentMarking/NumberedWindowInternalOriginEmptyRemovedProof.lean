module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginEmptyRemovedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapLocalIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginEmptyRemovedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply cancelSuc)
open ID1Completion.InternalListCodec (headCode tailCode)
open ID1Completion.InternalListCodecDecompositionSupportProof (reconstructNonzero nonzeroRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough renameParser)
open NumberedWindowInternalDirectInsertedRowCases (exactOpenInsertedRowCases)
open NumberedWindowInternalDirectInsertedScan (exactOpenScanCons)
open NumberedWindowInternalDirectInsertedScanTargets (rowAccept loopAccept)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalDirectTargetMapIntroTargets (D)
open NumberedWindowInternalDirectTargetMapLocalIntroProof (exact_OpenTargetProjectionNil)
open NumberedWindowInternalOriginEmptyRemovedTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenScratchNonzeroCases : ExactOpenScratchNonzeroCases := by
  intro B α Γ code goal positive next
  apply programCases headCode ![code] goal
  intro β j Δ h hj head
  rw [inputsRename] at head
  have pos := renameInto positive j Δ hj
  rw [nonzeroRename] at pos
  apply programCases tailCode ![code.relabel j] (goal.relabel j)
  intro γ k Θ t hk tail
  rw [inputsRename] at tail
  have pos' := renameInto pos k Θ hk
  rw [nonzeroRename] at pos'
  have head' : D B Θ (unary headCode (h.relabel k) ((code.relabel j).relabel k)) := by
    have moved := renameInto head k Θ hk
    change D B Θ ((unary headCode h (code.relabel j)).relabel k) at moved
    rw [unaryRename] at moved
    exact moved
  have c := reconstructNonzero ((code.relabel j).relabel k) (h.relabel k) t pos' head' tail
  rw [formulaRelabelComposition]
  exact next γ (k ∘ j) Θ (h.relabel k) t (keepThrough j k hj hk)
    (by simpa only [Term.relabel_relabel] using c)

private theorem noEmptyMember (dom : OTerm α) (m : D B Γ (memberGraph z dom)) :
    D B Γ (⊥ : Formula α) := by
  have m' := nilRecover memberBase memberStep (suc z) ![dom] m
  have zero : D B Γ (programGraph memberBase z ![dom]) := constantZeroValue ![dom]
  obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![dom] m' zero
  exact ⟨sucNeZeroApply bad⟩

private theorem noRow (r : Program 3) (removed row : OTerm α)
    (empty : D B Γ (unary parser (suc z) removed))
    (valid : D B Γ (rowAccept r row removed)) : D B Γ (⊥ : Formula α) := by
  apply exactOpenInsertedRowCases r B α Γ removed row (⊥ : Formula α) valid
  intro β j Δ decoded _ dom _ keep report
  have empty' := renameParser removed z empty j Δ keep
  rw [zRelabel] at empty'
  obtain ⟨same⟩ := valueUnique parser (suc decoded) (suc z) ![removed.relabel j] report.parsed empty'
  obtain ⟨decodedRow⟩ := report.original
  have member : D B Δ (memberGraph decoded dom) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight decodedRow)⟩
  have badMember := headTransport scratchMember (suc z) decoded z ![dom] ⟨cancelSuc same⟩ member
  exact noEmptyMember dom badMember

theorem exact_OpenEmptyRemovedScanZero : ExactOpenEmptyRemovedScanZero := by
  intro r B α Γ rows removed empty accept
  let nz := (eqn rows z).not
  let Δ := nz :: Γ
  have hn : D B Δ nz := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have bad : D B Δ (⊥ : Formula α) := by
    apply exact_OpenScratchNonzeroCases B α Δ rows (⊥ : Formula α) hn
    intro β j Ω row tail positive cell
    have survive : ∀ p ∈ Γ, p.relabel j ∈ Ω :=
      fun p hp => positive p (List.mem_cons_of_mem _ hp)
    have parsed := renameParser removed z empty j Ω survive
    rw [zRelabel] at parsed
    have accept' := renameInto accept j Ω survive
    rw [loopRename] at accept'
    obtain ⟨h⟩ := exactOpenScanCons r B β Ω (rows.relabel j) row tail
      (removed.relabel j) cell accept'
    exact noRow r (removed.relabel j) row parsed ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨bad⟩ := bad
  exact ⟨Derivation.classical bad⟩

theorem exact_OpenEmptyRemovedProjectionZero : ExactOpenEmptyRemovedProjectionZero := by
  intro r B α Γ rows removed projected empty accept proj
  have nothing := exact_OpenEmptyRemovedScanZero r B α Γ rows removed empty accept
  have atNil := headTransport scratchTargets (suc projected) rows z Fin.elim0 nothing proj
  obtain ⟨same⟩ := valueUnique scratchTargets (suc projected) (suc z) ![z] atNil
    (exact_OpenTargetProjectionNil B α Γ)
  exact ⟨cancelSuc same⟩

#print axioms exact_OpenScratchNonzeroCases
#print axioms exact_OpenEmptyRemovedScanZero
#print axioms exact_OpenEmptyRemovedProjectionZero

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginEmptyRemovedProof
