module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentLeafProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedMemoZeroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open ID1Completion.InternalLessThan (constantOne)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt)
open NumberedWindowInternalCoverSelectedMemoZeroProof (exact_OpenCoverSelectedMemoZero)
open NumberedWindowInternalCoverHeaderFieldsOpenProof (exact_OpenCoverHeaderFields)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntaxUpdate)
open NumberedWindowInternalCoverAuxSyntaxOpenParentProof (exact_OpenCoverAuxSyntaxParent)
open NumberedWindowInternalAuxMeasureOpenDataProof (bothChildBounds)
open NumberedWindowInternalCoverAuxFragmentGuardTargets
open NumberedWindowInternalCoverAuxFragmentLeafProof (headerZeroOfNotOne exact_OpenCoverAuxFragmentLeaf)

theorem exact_OpenCoverAuxFragmentCases : ExactOpenCoverAuxFragmentCases := by
  intro body α Γ raw goal valid leaf fork
  let P := headerAt 6 4 raw
  apply formulaCases P goal
  · have actualHeader : Nonempty (Derivation body (P :: Γ) (headerAt 6 4 raw)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply exact_OpenCoverHeaderFields 6 4 body α (P :: Γ) raw goal actualHeader
    intro β j Δ fields keep len reports packing
    rcases fields with _ | ⟨dom,_ | ⟨cod,_ | ⟨fn,_ | ⟨arg,_ | ⟨extra,rest⟩⟩⟩⟩⟩ <;> simp at len
    have retain : ∀ q ∈ Γ, q.relabel j ∈ Δ := fun q h => keep q (List.mem_cons_of_mem P h)
    let q := raw.relabel j
    let key := auxiliaryTerm dom cod fn arg
    change Nonempty (Derivation body Δ (eqn q key)) at packing
    have accepted := renameInto valid j Δ retain
    simp only [unaryRename,zRelabel,sucRelabel] at accepted
    have atKey := moveUnary fragmentGuard (suc z) q key packing accepted
    obtain ⟨parts⟩ := exact_OpenCoverAuxSyntaxParent fragmentLeaf (constantOne 1) body β Δ dom cod fn arg atKey
    let both := Derivation.conjunctionRight parts
    have bounds := bothChildBounds (body := body) (Γ := Δ) dom cod fn arg
    obtain ⟨fnSmall⟩ := bounds.1
    obtain ⟨argSmall⟩ := bounds.2
    obtain ⟨same⟩ := packing
    exact fork β j Δ dom cod fn arg retain reports ⟨same⟩
      ⟨orderRight fn (symm same) fnSmall⟩
      ⟨orderRight arg (symm same) argSmall⟩
      ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  · have notAux : Nonempty (Derivation body (P.not :: Γ) (unary termShape z raw)) :=
      headerZeroOfNotOne 6 4 raw ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply zeroSuccessorCases (P.not :: Γ) raw goal
    · let Z := eqn raw z
      have rawAtZero : Nonempty (Derivation body (Z :: P.not :: Γ) (eqn raw z)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have success := moveUnary fragmentGuard (suc z) raw z rawAtZero (withHyp (withHyp valid P.not) Z)
      have zero := exact_OpenCoverSelectedMemoZero (auxSyntaxUpdate fragmentLeaf (constantOne 1)) body α
        (Z :: P.not :: Γ)
      obtain ⟨bad⟩ := valueUnique fragmentGuard (suc z) z ![z] success zero
      exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
    · intro β j Δ prior keep eq
      have retain : ∀ q ∈ Γ, q.relabel j ∈ Δ := fun q h => keep q (List.mem_cons_of_mem P.not h)
      have accepted := renameInto valid j Δ retain
      have no := renameInto notAux j Δ keep
      simp only [unaryRename,zRelabel,sucRelabel] at accepted no
      have atKey := moveUnary fragmentGuard (suc z) (raw.relabel j) (suc prior) eq accepted
      have noAux := moveUnary termShape z (raw.relabel j) (suc prior) eq no
      have noLambda := exact_OpenCoverAuxFragmentLeaf body β Δ prior atKey noAux
      exact leaf β j Δ prior retain eq noLambda noAux

#print axioms exact_OpenCoverAuxFragmentCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentCasesProof
