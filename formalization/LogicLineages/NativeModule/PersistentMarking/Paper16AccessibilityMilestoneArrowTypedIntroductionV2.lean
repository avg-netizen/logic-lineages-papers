module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneGroundTypedIntroductionV2
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypedIntroductionV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchControlChecks
  (exact_DispatchControlAST exact_DispatchObjectTypeCode)
open NumberedWindowInternalFreshProbeDispatchObjectGraphProof (memberAt)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalProbeTargets (OTerm typeCode typedAt)
open NumberedWindowProbeCode (code)
open Paper16AccessibilityMilestoneGroundTypedIntroductionV2 (exact_RequestedTypeTestFromResult)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)

attribute [local irreducible] programGraph

private theorem predecessorReport {n : Nat} {body : Positive (Fin 1)}
    {α : Type} {Γ : List (Formula α)} (p : Program n) (xs : Fin n → OTerm α) (u : OTerm α)
    (report : Nonempty (Derivation body Γ (programGraph p (suc u) xs))) :
    Nonempty (Derivation body Γ (programGraph (afterPredecessor p) u xs)) := by
  have pred : Nonempty (Derivation body Γ (programGraph predOne u ![suc u])) := by
    rw [exact_DispatchControlAST.2.2.1]
    exact predecessorSuccessor u
  unfold afterPredecessor
  apply compositionValue predOne _ u xs ![suc u] pred
  intro i
  obtain rfl := Fin.eq_zero i
  exact report

/-- Introduce the installed arrow type from its original physical reports.
The caller supplies the selected fresh and option-application outputs,
the application guard, and the recursive codomain typing. -/
theorem exact_OriginalArrowTypedIntroduction {S : Spine.Signature} {K : List Ty}
    (A : InstalledWindow S K (sourceWindow K)) (c : Nat) (σ τ : ProbeTy)
    (listed : (.arrow σ τ : ProbeTy) ∈ sourceWindow K)
    {α : Type} {Γ : List (Formula α)} (q u v : OTerm α)
    (prior : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph A.probes.priorTyped (suc z) ![numeral (typeCode (.arrow σ τ)), q])))
    (result : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph rawResult (numeral (typeCode (.arrow σ τ))) ![q])))
    (fresh : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph (chosenA A.probes) (suc u) ![q])))
    (optionApp : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph A.probes.optionApplication (suc v) ![q, u])))
    (app : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph A.probes.applicationGuard (suc z) ![q, u, v])))
    (codomain : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (typedAt (chosenH A.probes (sourceWindow K)) τ v))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (typedAt (chosenH A.probes (sourceWindow K)) (.arrow σ τ) q)) := by
  let body := sourceBody A.presentation c
  let W := sourceWindow K
  let leaves := chosenLeaves A.probes
  let arrow : ProbeTy := .arrow σ τ
  let t : OTerm α := numeral (typeCode arrow)
  let childVerifier := verify leaves τ
  have request := exact_RequestedTypeTestFromResult t q result
  have base : Nonempty (Derivation body Γ (programGraph leaves.baseTyped (suc z) ![t, q])) := by
    change Nonempty (Derivation body Γ
      (programGraph (baseWithResult A.probes.priorTyped) (suc z) ![t, q]))
    rw [baseWithResult, exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept A.probes.priorTyped requestedTypeTest ![t, q] prior request
  have codeValue : Nonempty (Derivation body Γ
      (programGraph (literal 1 (code arrow)) t ![q])) := by
    rw [exact_DispatchControlAST.2.1, exact_DispatchObjectTypeCode]
    exact constantValue 1 (typeCode arrow) ![q]
  have baseLeaf : Nonempty (Derivation body Γ (programGraph (typeLeaf leaves arrow) (suc z) ![q])) := by
    unfold typeLeaf
    exact compositionValue leaves.baseTyped
      (Fin.cons (literal 1 (code arrow)) (Fin.cons (.projection (0 : Fin 1)) Fin.elim0))
      (suc z) ![q] ![t, q] base
      (fun i => Fin.cases codeValue
        (Fin.cases (projectionValue (0 : Fin 1) ![q]) (fun j => Fin.elim0 j)) i)
  have childListed : τ ∈ W := A.valid.2.1 σ τ listed
  have child : Nonempty (Derivation body Γ (programGraph childVerifier (suc z) ![v])) :=
    (memberAt leaves W τ childListed (suc z) v).mp codomain
  let childAtThird : Program 3 :=
    .composition childVerifier (Fin.cons (.projection (2 : Fin 3)) Fin.elim0)
  have childGraph : Nonempty (Derivation body Γ (programGraph childAtThird (suc z) ![q, u, v])) := by
    apply compositionValue childVerifier (Fin.cons (.projection (2 : Fin 3)) Fin.elim0)
      (suc z) ![q, u, v] ![v] child
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (2 : Fin 3) ![q, u, v]
  have guardGraph : Nonempty (Derivation body Γ
      (programGraph (resultGuard leaves childVerifier) (suc z) ![q, u, v])) := by
    rw [resultGuard, exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept leaves.applicationGuard childAtThird ![q, u, v] app childGraph
  let appSlots : Fin 3 → Program 2 := Fin.cons (.projection (0 : Fin 2))
    (Fin.cons (.projection (1 : Fin 2)) (Fin.cons (afterPredecessor leaves.applicationCode) Fin.elim0))
  let appBranch := Program.composition (resultGuard leaves childVerifier) appSlots
  have appBranchGraph : Nonempty (Derivation body Γ (programGraph appBranch (suc z) ![q, u])) := by
    apply compositionValue (resultGuard leaves childVerifier) appSlots (suc z) ![q, u] ![q, u, v] guardGraph
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
    · exact projectionValue (0 : Fin 2) ![q, u]
    · exact projectionValue (1 : Fin 2) ![q, u]
    · exact predecessorReport leaves.applicationCode ![q, u] v optionApp
  have appPart : Nonempty (Derivation body Γ
      (programGraph (applicationPart leaves childVerifier) (suc z) ![q, u])) := by
    unfold applicationPart
    rw [exact_DispatchControlAST.2.2.2.2.1, exact_DispatchControlAST.1]
    exact successorBranchIntro leaves.applicationCode (constantZero 2) appBranch
      (suc z) v ![q, u] optionApp appBranchGraph
  let freshSlots : Fin 2 → Program 1 := Fin.cons (.projection (0 : Fin 1))
    (Fin.cons (afterPredecessor leaves.fresh) Fin.elim0)
  let freshBranch := Program.composition (applicationPart leaves childVerifier) freshSlots
  have freshBranchGraph : Nonempty (Derivation body Γ (programGraph freshBranch (suc z) ![q])) := by
    apply compositionValue (applicationPart leaves childVerifier) freshSlots (suc z) ![q] ![q, u] appPart
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
    · exact projectionValue (0 : Fin 1) ![q]
    · exact predecessorReport leaves.fresh ![q] u fresh
  have arrowGraph : Nonempty (Derivation body Γ
      (programGraph (arrowPart leaves childVerifier) (suc z) ![q])) := by
    unfold arrowPart
    rw [exact_DispatchControlAST.2.2.2.2.1, exact_DispatchControlAST.1]
    exact successorBranchIntro leaves.fresh (constantZero 1) freshBranch
      (suc z) u ![q] fresh freshBranchGraph
  apply (memberAt leaves W arrow listed (suc z) q).mpr
  change Nonempty (Derivation body Γ
    (programGraph (bothOne (typeLeaf leaves arrow) (arrowPart leaves childVerifier)) (suc z) ![q]))
  rw [exact_DispatchControlAST.2.2.2.2.2]
  exact conjunctionAccept (typeLeaf leaves arrow) (arrowPart leaves childVerifier) ![q] baseLeaf arrowGraph

#print axioms exact_OriginalArrowTypedIntroduction

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypedIntroductionV2
