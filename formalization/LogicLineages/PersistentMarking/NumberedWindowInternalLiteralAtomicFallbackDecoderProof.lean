module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTickNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingFirstTickProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFallbackDecoderProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (branch constantZero conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot atomicFallback rootBottomComparison)
open NumberedWindowInternalLiteralDescendingFirstTickProof (FrameDecoder)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem contradictZero (xs : Fin 3 → OTerm α) (n : OTerm α) (goal : Formula α)
    (h : D B Γ (programGraph (constantZero 3) (suc n) xs)) : D B Γ goal := by
  obtain ⟨eq⟩ := valueUnique (constantZero 3) (suc n) z xs h (constantZeroValue xs)
  exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩

theorem exact_OpenAtomicFallbackUnderlying (P : Program 3) (q w r n : OTerm α)
    (held : D B Γ (programGraph (atomicFallback P) (suc n) ![q,w,r])) :
    D B Γ (programGraph P (suc n) ![q,w,r]) := by
  let F := onRaw freeTest 0
  let T := onRaw bottomTest 0
  let C := constantZero 3
  apply optionGraphCases F ![q,w,r] _
  · intro β j Δ keep noF
    rw [tripleInputsRename] at noF
    simp only [programRename,tripleInputsRename,sucRelabel]
    let xs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
    have h := renameInto held j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at h
    have branchOk := zeroBranchElim F (branch T P C) C (suc (n.relabel j)) xs noF h
    apply optionGraphCases T xs _
    · intro γ m Ω stay noT
      simp only [xs,tripleInputsRename] at noT
      simp only [xs,programRename,tripleInputsRename,sucRelabel]
      have h' := renameInto branchOk m Ω stay
      simp only [xs,programRename,tripleInputsRename,sucRelabel] at h'
      exact zeroBranchElim T P C _ _ noT h'
    · intro γ m Ω k stay yes
      simp only [xs,tripleInputsRename] at yes
      simp only [xs,programRename,tripleInputsRename,sucRelabel]
      have h' := renameInto branchOk m Ω stay
      simp only [xs,programRename,tripleInputsRename,sucRelabel] at h'
      exact contradictZero _ _ _ (successorBranchElim T P C _ k _ yes h')
  · intro β j Δ k keep yes
    rw [tripleInputsRename] at yes
    simp only [programRename,tripleInputsRename,sucRelabel]
    have h := renameInto held j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at h
    exact contradictZero _ _ _ (successorBranchElim F (branch T P C) C _ k _ yes h)

/-- The stronger fallback still has the same exact descending decoder
on every positive physical frame. No callback calibration is used. -/
theorem exact_OpenAtomicFallbackDecoder (P : Program 3) (decode : FrameDecoder P) :
    FrameDecoder (atomicFallback P) := by
  intro B α Γ q w r n goal held use
  exact decode B α Γ q w r n goal (exact_OpenAtomicFallbackUnderlying P q w r n held) use

/-- At a physically established non-atom, peel the new root guard on
the same original returned value and exact witness. -/
theorem exact_OpenAtomicRootNonAtom (P : Program 3) (q w r out : OTerm α)
    (noF : D B Γ (unary freeTest z q)) (noT : D B Γ (unary bottomTest z q))
    (held : D B Γ (programGraph (atomicRoot P) out ![q,w,r])) :
    D B Γ (programGraph P out ![q,w,r]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  have first := zeroBranchElim (onRaw freeTest 0)
    (branch (onRaw bottomTest 0) P (constantZero 3)) (conjunction P rootBottomComparison)
    out xs (onTape freeTest 0 z xs noF) held
  exact zeroBranchElim (onRaw bottomTest 0) P (constantZero 3) out xs (onTape bottomTest 0 z xs noT) first

#print axioms exact_OpenAtomicFallbackUnderlying
#print axioms exact_OpenAtomicFallbackDecoder
#print axioms exact_OpenAtomicRootNonAtom
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFallbackDecoderProof
