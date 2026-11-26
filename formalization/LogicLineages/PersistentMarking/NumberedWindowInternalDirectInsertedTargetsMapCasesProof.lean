module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapCasesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapCases
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalDirectInsertedTargetsMapTargets
open NumberedWindowInternalDirectInsertedTargetsMapCasesTargets
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename unaryRename)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def mappedCall : Program 1 := .composition scratchTargets (Fin.cons parserPayload Fin.elim0)

private theorem payloadReport (raw decoded : OrdinaryArithmetic.Term α)
    (p : Nonempty (Derivation B Γ (unary parser (suc decoded) raw))) :
    Nonempty (Derivation B Γ (unary parserPayload decoded raw)) := by
  apply compositionValue predecessor (Fin.cons parser Fin.elim0) decoded ![raw]
    ![suc decoded] (predecessorSuccessor decoded)
  intro i
  obtain rfl := Fin.eq_zero i
  exact p

private theorem rejectZero (raw result : OrdinaryArithmetic.Term α)
    (p : Nonempty (Derivation B Γ (unary parser z raw)))
    (h : Nonempty (Derivation B Γ (unary insertedTargets (suc result) raw))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  have failed := zeroBranchElim parser (constantZero 1) mappedCall (suc result) ![raw] p h
  obtain ⟨bad⟩ := valueUnique (constantZero 1) (suc result) z ![raw] failed
    (constantZeroValue ![raw])
  exact ⟨sucNeZeroApply bad⟩

private theorem scratchReport (raw decoded result : OrdinaryArithmetic.Term α)
    (p : Nonempty (Derivation B Γ (unary parser (suc decoded) raw)))
    (h : Nonempty (Derivation B Γ (unary insertedTargets (suc result) raw))) :
    Nonempty (Derivation B Γ (unary scratchTargets (suc result) decoded)) := by
  have ran := successorBranchElim parser (constantZero 1) mappedCall
    (suc result) decoded ![raw] p h
  apply compositionRecover scratchTargets (Fin.cons parserPayload Fin.elim0)
    (suc result) ![raw] ![decoded] ran
  intro i
  obtain rfl := Fin.eq_zero i
  exact payloadReport raw decoded p

theorem exactOpenRawMapCases : ExactOpenRawMapCases := by
  intro B α Γ raw result goal h next
  apply optionGraphCases parser ![raw] goal
  · intro β j Δ keep failed
    rw [inputsRename] at failed
    have held : Nonempty (Derivation B Δ (unary insertedTargets (suc (result.relabel j))
        (raw.relabel j))) := by
      simpa only [unaryRename,sucRelabel] using renameInto h j Δ keep
    obtain ⟨bad⟩ := rejectZero (raw.relabel j) (result.relabel j) failed held
    exact ⟨Derivation.explosion bad⟩
  · intro β j Δ decoded keep parsed
    rw [inputsRename] at parsed
    have held : Nonempty (Derivation B Δ (unary insertedTargets (suc (result.relabel j))
        (raw.relabel j))) := by
      simpa only [unaryRename,sucRelabel] using renameInto h j Δ keep
    exact next β j Δ decoded keep parsed
      (scratchReport (raw.relabel j) decoded (result.relabel j) parsed held)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapCases
