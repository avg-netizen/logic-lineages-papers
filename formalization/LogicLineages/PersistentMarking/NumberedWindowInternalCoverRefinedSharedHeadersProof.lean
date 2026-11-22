module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedMemoZeroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedHeadersProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc eqnRelabel zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverSelectedValidityTargets
open NumberedWindowInternalCoverSelectedValidityOpenProof (observeHeaders)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverSelectedMemoZeroProof (exact_OpenCoverSelectedMemoZero)
open NumberedWindowInternalCoverRefinedSharedStepProof (exact_OpenCoverRefinedStep)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets

attribute [local irreducible] programGraph

private theorem orRename {α β : Type} (p q : Formula α) (j : α → β) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

theorem headersRename {α β : Type} (xs : List (Nat × Nat)) (q : OTerm α) (j : α → β) :
    (headersAt xs q).relabel j = headersAt xs (q.relabel j) := by
  induction xs with
  | nil => simp only [headersAt,eqnRelabel,sucRelabel,zRelabel]
  | cons pair rest ih =>
    rcases pair with ⟨tag,arity⟩
    simp only [headersAt,orRename,ih,headerAt,unaryRename,sucRelabel,zRelabel]

theorem exact_OpenCoverRefinedSharedHeaders : ExactOpenCoverRefinedSharedHeaders := by
  intro V T body α Γ raw parent
  let R := refinedUpdate V T
  let Q := refinedSyntax V T
  apply zeroSuccessorCases Γ raw (headersAt layout raw)
  · have atZero := moveUnary Q (suc z) raw z
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp parent (eqn raw z))
    have base := exact_OpenCoverSelectedMemoZero R body α (eqn raw z :: Γ)
    obtain ⟨bad⟩ := valueUnique Q (suc z) z ![z] atZero base
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ prior keep eq
    rw [headersRename]
    let key := raw.relabel j
    have actual := renameInto parent j Δ keep
    simp only [unaryRename,sucRelabel,zRelabel] at actual
    have successor := moveUnary Q (suc z) key (suc prior) eq actual
    apply exact_OpenCoverSharedMemoRowCases R body β Δ prior (suc z) (headersAt layout key) successor
    intro γ k Ξ old retain row
    rw [headersRename]
    simp only [sucRelabel,zRelabel] at row
    have same := renameInto eq k Ξ retain
    simp only [eqnRelabel,sucRelabel] at same
    obtain ⟨same⟩ := same
    have physical := (exact_OpenCoverRefinedStep V T body γ Ξ (prior.relabel k) old row).2
    have installed := moveUnary (headerAny layout) (suc z) (suc (prior.relabel k)) (key.relabel k)
      ⟨symm same⟩ physical
    exact observeHeaders layout (key.relabel k) installed

#print axioms exact_OpenCoverRefinedSharedHeaders

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedHeadersProof
