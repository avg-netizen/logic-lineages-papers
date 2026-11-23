module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceOpenIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalZeroRankAdvance

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Install the rank-zero filter around the actual successful optional run
without changing the input terms, raw output, or open arithmetic body. -/
theorem exact_InstallOpenZeroRankOutput {n : Nat} (g : Program 1) (A : Program n)
    (xs : Fin n → OTerm α) (y : OTerm α)
    (actual : Nonempty (Derivation B Γ (programGraph A (suc y) xs)))
    (rank : Nonempty (Derivation B Γ (unary g z y))) :
    Nonempty (Derivation B Γ (programGraph (zeroOutput g A) (suc y) xs)) := by
  have pr : Nonempty (Derivation B Γ (programGraph (unaryAfter predecessor A) y xs)) := by
    apply compositionValue predecessor (fun _ : Fin 1 => A) y xs ![suc y] (predecessorSuccessor y)
    intro i
    obtain rfl := Fin.eq_zero i
    exact actual
  have zr : Nonempty (Derivation B Γ (programGraph (resultRank g A) z xs)) := by
    apply compositionValue g (fun _ : Fin 1 => unaryAfter predecessor A) z xs ![y] rank
    intro i
    obtain rfl := Fin.eq_zero i
    exact pr
  exact zeroBranchIntro (resultRank g A) A (constantZero n) (suc y) xs zr actual

#print axioms exact_InstallOpenZeroRankOutput
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceOpenIntroProof
