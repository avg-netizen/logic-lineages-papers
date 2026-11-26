module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverBranchTapeForwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro zeroBranchElim successorBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases outputTransport programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverLocalGraphForwardTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem carryForward {n : Nat} (P Q : Program n) (xs : Fin n → OTerm α)
    (hre : TapeForward P Q body Γ xs) {β : Type} (j : α → β) (Δ : List (Formula β))
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    TapeForward P Q body Δ (fun i => (xs i).relabel j) := by
  intro γ g Ξ out retain actual
  simp only [Term.relabel_relabel] at actual ⊢
  exact hre γ (g ∘ j) Ξ out (keepThrough j g keep retain) actual

private theorem controlled {n : Nat} (xs : Fin n → OTerm α) (C C' P P' Q Q' : Program n)
    (out ctrl : OTerm α)
    (forwardP : TapeForward P P' body Γ xs) (forwardQ : TapeForward Q Q' body Γ xs)
    (oldC : Nonempty (Derivation body Γ (programGraph C ctrl xs)))
    (newC : Nonempty (Derivation body Γ (programGraph C' ctrl xs)))
    (oldBranch : Nonempty (Derivation body Γ (programGraph (branch C P Q) out xs))) :
    Nonempty (Derivation body Γ (programGraph (branch C' P' Q') out xs)) := by
  apply zeroSuccessorCases Γ ctrl _
  · let E := eqn ctrl z
    let Δ := E :: Γ
    have eq : Nonempty (Derivation body Δ E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zeroOld := outputTransport C ctrl z xs eq (withHyp oldC E)
    have zeroNew := outputTransport C' ctrl z xs eq (withHyp newC E)
    have old := zeroBranchElim C P Q out xs zeroOld (withHyp oldBranch E)
    have keep (f : Formula α) (h : f ∈ Γ) : f.relabel id ∈ Δ := by
      rw [ID1Completion.InternalFiniteBlocksSubstitutionProof.renameIdentity]
      exact List.mem_cons_of_mem E h
    have same : (fun i : Fin n => (xs i).relabel id) = xs :=
      funext fun i => Term.relabel_id (xs i)
    have atP := forwardP α id Δ out keep (Eq.mpr (congrArg
      (fun tape => Nonempty (Derivation body Δ (programGraph P out tape))) same) old)
    rw [same] at atP
    exact zeroBranchIntro C' P' Q' out xs zeroNew atP
  · intro β j Δ k keep eq
    simp only [programRename]
    let ys := fun i => (xs i).relabel j
    let o := out.relabel j
    let c := ctrl.relabel j
    have old := renameInto oldC j Δ keep
    have new := renameInto newC j Δ keep
    have oldOut := renameInto oldBranch j Δ keep
    simp only [programRename] at old new oldOut
    have before := outputTransport C c (suc k) ys eq old
    have after := outputTransport C' c (suc k) ys eq new
    have prior := successorBranchElim C P Q o k ys before oldOut
    exact successorBranchIntro C' P' Q' o k ys after (forwardQ β j Δ o keep prior)

theorem exact_OpenCoverBranchTapeForward : ExactOpenCoverBranchTapeForward := by
  intro body n α Γ xs C C' P P' Q Q' cForward pForward qForward β j Δ out keep actual
  let ys := fun i => (xs i).relabel j
  let S := programGraph (branch C' P' Q') out ys
  apply programCases C ys S
  intro γ k Ξ ctrl retain old
  let jk := k ∘ j
  let zs := fun i => (xs i).relabel jk
  have both := keepThrough j k keep retain
  have branchOld := renameInto actual k Ξ retain
  simp only [programRename,Term.relabel_relabel] at branchOld
  simp only [ys,Term.relabel_relabel] at old
  have new := cForward γ jk Ξ ctrl both old
  simp only [S,programRename,ys,Term.relabel_relabel]
  exact controlled zs C C' P P' Q Q' (out.relabel k) ctrl
    (carryForward P P' xs pForward jk Ξ both) (carryForward Q Q' xs qForward jk Ξ both) old new branchOld

#print axioms carryForward
#print axioms exact_OpenCoverBranchTapeForward

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverBranchTapeForwardProof
