module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranchesTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranchesPaymentProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranchesProof
import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceMatrixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranches
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open ActualFiniteOrderBranches (Pattern realized)
open OriginalPrintedPlainMatrixOrderBranches (renamed BranchAccepts exactPrintedOrderBranchesCover)
open OriginalMatrixPaidCongruence (exactPaidCongruenceMatrix)

private theorem branchMode (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (branch : Pattern) :
    BranchAccepts f θ known gates p positive branch ↔
      CompiledAccepts f θ known gates p positive branch := by
  have same := exactPaidCongruenceMatrix f B hf (realized θ branch)
    (renamed known gates p branch) (exactInitialModularPayment B (realized θ branch) known gates p branch)
  constructor
  · rintro ⟨xs,actual,accepts⟩
    exact ⟨xs,(same _).mp actual,accepts⟩
  · rintro ⟨xs,compiled,accepts⟩
    exact ⟨xs,(same _).mpr compiled,accepts⟩

theorem exactPrintedModularBranches : ExactPrintedModularBranches := by
  intro f B hf θ known gates p plain prior positive
  have original := exactPrintedOrderBranchesCover f θ known gates p plain prior positive
  constructor
  · intro h
    obtain ⟨branch,member,guard,pr,accepts⟩ := original.mp h
    exact ⟨branch,member,guard,pr,(branchMode f B hf θ known gates p positive branch).mp accepts⟩
  · rintro ⟨branch,member,guard,pr,accepts⟩
    exact original.mpr ⟨branch,member,guard,pr,
      (branchMode f B hf θ known gates p positive branch).mpr accepts⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranches
