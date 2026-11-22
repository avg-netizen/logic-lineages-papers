module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardBasicsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverBranchTapeForwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBranchWrappersForwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverLocalGraphForwardTargets
open NumberedWindowInternalCoverLocalGraphForwardBasicsProof (tapeRefl)
open NumberedWindowInternalCoverBranchTapeForwardProof (exact_OpenCoverBranchTapeForward)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} {xs : Fin 2 → OTerm α}

theorem carryGuardWrapper (C D P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (branch C P (branch D (constantZero 2) P))
      (branch C Q (branch D (constantZero 2) Q)) body Γ xs := by
  have guarded := exact_OpenCoverBranchTapeForward body 2 α Γ xs D D (constantZero 2) (constantZero 2)
    P Q (tapeRefl D xs) (tapeRefl (constantZero 2) xs) pq
  exact exact_OpenCoverBranchTapeForward body 2 α Γ xs C C P Q _ _ (tapeRefl C xs) pq guarded

theorem carryOutputWrapper (C R S P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (branch C P (branch P R S)) (branch C Q (branch Q R S)) body Γ xs := by
  have guarded := exact_OpenCoverBranchTapeForward body 2 α Γ xs P Q R R S S pq
    (tapeRefl R xs) (tapeRefl S xs)
  exact exact_OpenCoverBranchTapeForward body 2 α Γ xs C C P Q _ _ (tapeRefl C xs) pq guarded

#print axioms carryGuardWrapper
#print axioms carryOutputWrapper

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBranchWrappersForwardProof
