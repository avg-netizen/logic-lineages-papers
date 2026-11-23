module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomBranchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomProof
import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomBranch
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph (programGraph equal)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue outputTransport zeroSuccessorCases valueUnique
    programRename equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeDispatchProgram (chooseBranch)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (branchEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSingletonBottomTargets (recognize packedSingletonBottom)
open NumberedWindowInternalSingletonBottom
  (exactNumericSingletonBottom exactOpenSingletonBottom exactDirectSingletonBottomTarget)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSingletonBottomBranchTargets

private theorem selectorValue (x w y : Nat) :
    evaluate sourceSelector (x ::ᵥ w ::ᵥ y ::ᵥ nil) = run recognize x := by
  unfold sourceSelector run
  rw [evaluate,vectorOne] <;> rfl

private theorem selectedValue (d : Program 3) (x w y : Nat) :
    evaluate (singletonGuard d) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if run recognize x = 1 ∧ y ≠ 0 then 0 else evaluate d (x ::ᵥ w ::ᵥ y ::ᵥ nil) := by
  change evaluate (chooseBranch sourceControl d
    (chooseBranch (.projection 2) d (constantZero 3))) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = _
  rw [branchEvaluation,branchEvaluation,sourceControl,GorbowVerifierNormalization.Proof.actualEvaluation.2,selectorValue]
  have target : evaluate (.projection (2 : Fin 3)) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = y := rfl
  rw [target]
  change (if (if run recognize x = 1 then 1 else 0) = 0 then
      evaluate d (x ::ᵥ w ::ᵥ y ::ᵥ nil) else
    if y = 0 then evaluate d (x ::ᵥ w ::ᵥ y ::ᵥ nil) else 0) = _
  by_cases hx : run recognize x = 1 <;> by_cases hy : y = 0 <;> simp [hx,hy]

theorem exactSingletonGuardSelection : ExactSingletonGuardSelection := by
  intro xs s i j r d old
  refine ⟨old.1,old.2.1,old.2.2.1,?_⟩
  intro x w y
  rw [selectedValue]
  by_cases hguard : run recognize x = 1 ∧ y ≠ 0
  · rw [if_pos hguard]
    obtain ⟨ctx,t,hx⟩ := (exactNumericSingletonBottom x).mp hguard.1
    have reject : NumberedWindowConcreteCheckers.direct xs s x w y = false := by
      cases hit : NumberedWindowConcreteCheckers.direct xs s x w y
      · rfl
      · rw [hx] at hit
        exact (hguard.2 (exactDirectSingletonBottomTarget xs s ctx t w y hit)).elim
    change 0 = (NumberedWindowConcreteCheckers.direct xs s x w y).toNat
    rw [reject] <;> rfl
  · rw [if_neg hguard]
    exact old.2.2.2 x w y

private theorem sourceReports {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (ctx t w y : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B Γ (programGraph sourceControl (suc z) ![packedSingletonBottom ctx t,w,y])) := by
  let x := packedSingletonBottom ctx t
  let xs : Fin 3 → OrdinaryArithmetic.Term α := ![x,w,y]
  apply normalizeAccept sourceSelector xs
  apply compositionValue recognize (fun _ : Fin 1 => .projection (0 : Fin 3)) (suc z) xs ![x]
  · exact exactOpenSingletonBottom B α Γ ctx t
  · intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 0 xs

private theorem targetAtSuccessor {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (d : Program 3) (x w y k : OrdinaryArithmetic.Term α)
    (hy : Nonempty (Derivation B Γ (eqn y (suc k))))
    (accepted : Nonempty (Derivation B Γ (programGraph (targetBranch d) (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term α := ![x,w,y]
  have projection : Nonempty (Derivation B Γ (programGraph (.projection 2) (suc k) xs)) :=
    outputTransport (.projection 2) y (suc k) xs hy (projectionValue 2 xs)
  have wrong := successorBranchElim (.projection 2) d (constantZero 3) (suc z) k xs projection accepted
  obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc z) z xs wrong (constantZeroValue xs)
  exact ⟨sucNeZeroApply bad⟩

private theorem acceptedTargetZero {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (d : Program 3) (x w y : OrdinaryArithmetic.Term α)
    (accepted : Nonempty (Derivation B Γ (programGraph (targetBranch d) (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (eqn y z)) := by
  apply zeroSuccessorCases Γ y (eqn y z)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro β ρ Δ k keep hy
    have coord : (fun n : Fin 3 => ((![x,w,y] : Fin 3 → OrdinaryArithmetic.Term α) n).relabel ρ) =
        ![x.relabel ρ,w.relabel ρ,y.relabel ρ] := by
      funext n
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) n
    have read : Nonempty (Derivation B Δ (programGraph (targetBranch d) (suc z)
        ![x.relabel ρ,w.relabel ρ,y.relabel ρ])) := by
      simpa only [programRename,sucRelabel,zRelabel,coord] using renameInto accepted ρ Δ keep
    obtain ⟨bad⟩ := targetAtSuccessor d (x.relabel ρ) (w.relabel ρ) (y.relabel ρ) k hy read
    exact ⟨Derivation.explosion bad⟩

theorem exactSymbolicSingletonCertificateTarget : ExactSymbolicSingletonCertificateTarget := by
  intro i j r d c α Γ ctx t y w
  dsimp only
  intro cert
  let x := packedSingletonBottom ctx t
  let S := data i j r (singletonGuard d)
  let B := sourceBody S c
  let args : Fin 3 → OrdinaryArithmetic.Term α := ![x,w,y]
  have accepted : Nonempty (Derivation B Γ (programGraph (singletonGuard d) (suc z) args)) :=
    (exact_CertificateRules i j r (singletonGuard d) true c B α Γ x y w).1 cert
  have report : Nonempty (Derivation B Γ (programGraph sourceControl (suc z) args)) :=
    sourceReports ctx t w y
  have inner := successorBranchElim sourceControl d (targetBranch d) (suc z) z args report accepted
  rw [equalEqn]
  exact acceptedTargetZero d x w y inner

end LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomBranch
