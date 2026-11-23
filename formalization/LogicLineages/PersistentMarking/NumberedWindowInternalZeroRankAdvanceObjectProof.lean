module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceObjectProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalZeroRankAdvance

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem actualRank {n : Nat} (g : Program 1) (A : Program n) (xs : Fin n → OTerm α)
    (y : OTerm α) (step : Nonempty (Derivation B Γ (programGraph A (suc y) xs)))
    (known : Nonempty (Derivation B Γ (programGraph (resultRank g A) z xs))) :
    Nonempty (Derivation B Γ (unary g z y)) := by
  have p : Nonempty (Derivation B Γ (unary predecessor y (suc y))) := predecessorSuccessor y
  have out : Nonempty (Derivation B Γ (programGraph (unaryAfter predecessor A) y xs)) := by
    apply compositionValue predecessor (fun _ : Fin 1 => A) y xs ![suc y] p
    intro j
    obtain rfl := Fin.eq_zero j
    exact step
  unfold resultRank unaryAfter at known
  apply compositionRecover g (fun _ : Fin 1 => unaryAfter predecessor A) z xs ![y] known
  intro j
  obtain rfl := Fin.eq_zero j
  exact out

/-- Opening an actual successful zero-output filtered original advance
(or other optional output) yields the same original run and an actual
same-body zero-rank report on its exact output. -/
theorem exact_OpenZeroRankOutput {n : Nat} (g : Program 1) (A : Program n)
    (xs : Fin n → OTerm α) (y : OTerm α)
    (held : Nonempty (Derivation B Γ (programGraph (zeroOutput g A) (suc y) xs))) :
    Nonempty (Derivation B Γ (programGraph A (suc y) xs ⊓ unary g z y)) := by
  unfold zeroOutput at held
  apply optionGraphCases (resultRank g A) xs _
  · intro β j Δ keep clear
    let tape : Fin n → OTerm β := fun i => (xs i).relabel j
    have h := renameInto held j Δ keep
    simp only [programRename,sucRelabel] at h
    have orig := zeroBranchElim (resultRank g A) A (constantZero n) (suc (y.relabel j)) tape clear h
    have zr := actualRank g A tape (y.relabel j) orig clear
    obtain ⟨r⟩ := orig
    obtain ⟨zv⟩ := zr
    simp only [ID1Completion.InternalRecursionGraphStepSyntaxProof.conjunctionRename,
      programRename,unaryRename,sucRelabel,zRelabel]
    exact ⟨Derivation.conjunctionIntroduction r zv⟩
  · intro β j Δ k keep positive
    let tape : Fin n → OTerm β := fun i => (xs i).relabel j
    have h := renameInto held j Δ keep
    simp only [programRename,sucRelabel] at h
    have bad := successorBranchElim (resultRank g A) A (constantZero n) (suc (y.relabel j)) k tape positive h
    obtain ⟨eq⟩ := valueUnique (constantZero n) (suc (y.relabel j)) z tape bad (constantZeroValue tape)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩

#print axioms exact_OpenZeroRankOutput
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceObjectProof
