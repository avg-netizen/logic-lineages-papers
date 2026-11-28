module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectGraphProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneGroundTypedIntroductionV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchObjectGraphProof (memberAt)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)

attribute [local irreducible] programGraph

/-- The actual field report pays the equality test for the requested type. -/
theorem exact_RequestedTypeTestFromResult {body : Positive (Fin 1)}
    {α : Type} {Γ : List (Formula α)} (t q : OTerm α)
    (result : Nonempty (Derivation body Γ (programGraph rawResult t ![q]))) :
    Nonempty (Derivation body Γ (programGraph requestedTypeTest (suc z) ![t, q])) := by
  have resultAt : Nonempty (Derivation body Γ (programGraph resultAtSecond t ![t, q])) := by
    unfold resultAtSecond
    apply compositionValue rawResult (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)
      t ![t, q] ![q] result
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (1 : Fin 2) ![t, q]
  have compare : Nonempty (Derivation body Γ (programGraph compareNumbers (suc z) ![t, t])) := by
    rw [exact_DispatchControlAST.2.2.2.1]
    exact equalityOfEqual t t ⟨refl t⟩
  unfold requestedTypeTest
  exact compositionValue compareNumbers
    (Fin.cons (.projection (0 : Fin 2)) (Fin.cons resultAtSecond Fin.elim0))
    (suc z) ![t, q] ![t, t] compare
    (fun i => Fin.cases (projectionValue (0 : Fin 2) ![t, q])
      (Fin.cases resultAt (fun j => Fin.elim0 j)) i)

/-- Introduce the ground branch using the installed prior type checker and
the actual result field of the same address. -/
theorem exact_OriginalGroundTypedIntroduction {S : Spine.Signature} {K : List Ty}
    (A : InstalledWindow S K (sourceWindow K)) (c : Nat) (ground : Ty.ground ∈ K)
    {α : Type} {Γ : List (Formula α)} (q : OTerm α)
    (prior : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph A.probes.priorTyped (suc z) ![z, q])))
    (result : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph rawResult z ![q]))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (typedAt (chosenH A.probes (sourceWindow K)) .ground q)) := by
  let body := sourceBody A.presentation c
  let leaves := chosenLeaves A.probes
  have listed : (.ground : ProbeTy) ∈ sourceWindow K :=
    List.mem_map.mpr ⟨Ty.ground, ground, rfl⟩
  change Nonempty (Derivation body Γ
    (programGraph (dispatch leaves (sourceWindow K)) (suc z) ![z, q]))
  apply (memberAt leaves (sourceWindow K) .ground listed (suc z) q).mpr
  have request := exact_RequestedTypeTestFromResult z q result
  have base : Nonempty (Derivation body Γ (programGraph leaves.baseTyped (suc z) ![z, q])) := by
    change Nonempty (Derivation body Γ
      (programGraph (baseWithResult A.probes.priorTyped) (suc z) ![z, q]))
    rw [baseWithResult, exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept A.probes.priorTyped requestedTypeTest ![z, q] prior request
  have zero : Nonempty (Derivation body Γ (programGraph (literal 1 0) z ![q])) := by
    rw [exact_DispatchControlAST.2.1]
    exact constantValue 1 0 ![q]
  exact compositionValue leaves.baseTyped
    (Fin.cons (literal 1 0) (Fin.cons (.projection (0 : Fin 1)) Fin.elim0))
    (suc z) ![q] ![z, q] base
    (fun i => Fin.cases zero
      (Fin.cases (projectionValue (0 : Fin 1) ![q]) (fun j => Fin.elim0 j)) i)

#print axioms exact_RequestedTypeTestFromResult
#print axioms exact_OriginalGroundTypedIntroduction

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneGroundTypedIntroductionV2
