module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (renameIdentity)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel eqnRelabel)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverArgumentGuardOpenCutProof (actualArgumentGuardSuccessor)
open NumberedWindowInternalCoverArgumentGuardTargets

theorem exact_OpenCoverArgumentGuardCases : ExactOpenCoverArgumentGuardCases := by
  intro G body α Γ raw goal rejected zero cons
  apply zeroSuccessorCases Γ raw goal
  · let Z := eqn raw z
    have keep : ∀ f ∈ Γ, f.relabel id ∈ Z :: Γ := by
      intro f h
      simpa only [renameIdentity] using List.mem_cons_of_mem Z h
    have eq : Nonempty (Derivation body (Z :: Γ) (eqn (raw.relabel id) z)) := by
      simpa only [Term.relabel_id] using
        (show Nonempty (Derivation body (Z :: Γ) Z) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    simpa only [renameIdentity] using zero α id (Z :: Γ) keep eq
  · intro β j Δ prior keep eq
    have state := renameInto rejected j Δ keep
    simp only [unaryRename,zRelabel] at state
    have actual := moveUnary (argumentReject G) z (raw.relabel j) (suc prior) eq state
    apply actualArgumentGuardSuccessor G prior (goal.relabel j) actual
    intro γ g Ξ h a retain row
    have priorEq := renameInto eq g Ξ retain
    simp only [eqnRelabel,sucRelabel,Term.relabel_relabel] at priorEq
    obtain ⟨e⟩ := priorEq
    obtain ⟨pack⟩ := row.packed
    obtain ⟨earlier⟩ := row.earlier
    rw [formulaRelabelComposition j g goal]
    exact cons γ (g ∘ j) Ξ h a (keepThrough j g keep retain)
      ⟨trans e pack⟩ ⟨orderRight a (symm e) earlier⟩ row.head row.tail

#print axioms exact_OpenCoverArgumentGuardCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenProof
