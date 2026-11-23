module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedPositiveUnitConjunctionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedMemoZeroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedPositiveUnitProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverSelectedMemoZeroProof (exact_OpenCoverSelectedMemoZero)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedSyntaxUpdate)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets
open NumberedWindowInternalCoverRefinedPositiveUnitConjunctionProof (conjunctionUnitFromPositive)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual same selected memo V has a unit report wherever its graph
has an actual successor output. Zero and arbitrary callbacks remain
literal programs; no numerical calibration implies this derivation. -/
theorem exact_OpenRefinedSyntaxUnitFromPositive (V TV : Program 1) (key out : OTerm α)
    (actual : Nonempty (Derivation body Γ (unary (refinedSyntax V TV) (suc out) key))) :
    Nonempty (Derivation body Γ (unary (refinedSyntax V TV) (suc z) key)) := by
  let R := refinedUpdate V TV
  let Q := refinedSyntax V TV
  apply zeroSuccessorCases Γ key _
  · have atZero := moveUnary Q (suc out) key z
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp actual (eqn key z))
    have seed := exact_OpenCoverSelectedMemoZero R body α (eqn key z :: Γ)
    obtain ⟨bad⟩ := valueUnique Q (suc out) z ![z] atZero seed
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ prior keep eq
    simp only [unaryRename,sucRelabel,zRelabel]
    have held := renameInto actual j Δ keep
    simp only [unaryRename,sucRelabel] at held
    have atSucc := moveUnary Q (suc (out.relabel j)) (key.relabel j) (suc prior) eq held
    apply exact_OpenCoverSharedMemoRowCases R body β Δ prior (suc (out.relabel j)) _ atSucc
    intro γ k Θ old retain row
    simp only [unaryRename,sucRelabel,zRelabel]
    have original := renameInto held k Θ retain
    simp only [unaryRename,sucRelabel] at original
    simp only [sucRelabel] at row
    let xs : Fin 4 → OTerm γ := ![prior.relabel k,old,z,z]
    let out' := (out.relabel j).relabel k
    have unit := conjunctionUnitFromPositive (sharedSyntaxUpdate V TV) headerOnRow xs out' row.update
    have same := valueUnique R (suc out') (suc z) xs row.update unit
    exact outputTransport Q (suc out') (suc z) ![(key.relabel j).relabel k] same original

#print axioms exact_OpenRefinedSyntaxUnitFromPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedPositiveUnitProof
