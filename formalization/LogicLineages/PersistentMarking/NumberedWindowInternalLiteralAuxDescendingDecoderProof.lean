module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingFirstTickProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxDescendingDecoderProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame)
open NumberedWindowInternalSparseRawTick (tagFiveTest)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (shapeReject)
open NumberedWindowInternalLiteralAuxFallback
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralDescendingFirstTickProof (FrameDecoder functionDecoder fallbackDecoder)

attribute [local irreducible] programGraph

/-- Exposing the auxiliary source does not hide the bound of the
underlying callback. Its own successor branch is the separately
proved descending tag-five frame, not a raw numeric reflection. -/
theorem exact_OpenAuxiliaryDecoderWith (other : Program 3) (decode : FrameDecoder other) :
    FrameDecoder (auxiliaryFallback other) := by
  intro B α Γ q w r n goal held use
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let P := bit sourceIsAux xs
  let T := bit tagFiveTest xs
  let F := branch tagFiveTest (constantZero 3) chosenFrame
  obtain ⟨original⟩ := held
  have yes : D B (P :: Γ) goal := by
    have src : D B (P :: Γ) P := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hit⟩ := successorBranchElim sourceIsAux other F (suc n) z xs src ⟨addHyp original _⟩
    have y : D B (T :: P :: Γ) goal := by
      have five : D B (T :: P :: Γ) T := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have v := successorBranchElim tagFiveTest (constantZero 3) chosenFrame (suc n) z xs five
        ⟨addHyp hit _⟩
      apply functionDecoder B α (T :: P :: Γ) q w r n goal v
      intro β j Δ x u y keep eq lt
      exact use β j Δ x u y (fun f hf => keep f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf))) eq lt
    have n' : D B (T.not :: P :: Γ) goal := by
      have no : D B (T.not :: P :: Γ) (programGraph tagFiveTest z xs) :=
        shapeReject _ _ 1 xs ⟨Derivation.hypothesis List.mem_cons_self⟩
      have bad := zeroBranchElim tagFiveTest (constantZero 3) chosenFrame (suc n) xs no ⟨addHyp hit _⟩
      obtain ⟨eq⟩ := valueUnique (constantZero 3) (suc n) z xs bad (constantZeroValue xs)
      exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
    obtain ⟨dy⟩ := y
    obtain ⟨dn⟩ := n'
    exact ⟨disjunctionElimination (excludedMiddle T)
      (Derivation.implicationIntroduction dy) (Derivation.implicationIntroduction dn)⟩
  have no : D B (P.not :: Γ) goal := by
    have noSource : D B (P.not :: Γ) (programGraph sourceIsAux z xs) :=
      shapeReject _ _ 0 xs ⟨Derivation.hypothesis List.mem_cons_self⟩
    have out := zeroBranchElim sourceIsAux other F (suc n) xs noSource ⟨addHyp original _⟩
    apply decode B α (P.not :: Γ) q w r n goal out
    intro β j Δ x u y keep eq lt
    exact use β j Δ x u y (fun f hf => keep f (List.mem_cons_of_mem _ hf)) eq lt
  obtain ⟨a⟩ := yes
  obtain ⟨b⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction a) (Derivation.implicationIntroduction b)⟩

theorem exact_OpenAuxiliaryDescendingDecoder (other : Program 3) :
    FrameDecoder (auxiliaryFallback (fallback other)) :=
  exact_OpenAuxiliaryDecoderWith (fallback other) (fallbackDecoder other)

#print axioms exact_OpenAuxiliaryDecoderWith
#print axioms exact_OpenAuxiliaryDescendingDecoder
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxDescendingDecoderProof
