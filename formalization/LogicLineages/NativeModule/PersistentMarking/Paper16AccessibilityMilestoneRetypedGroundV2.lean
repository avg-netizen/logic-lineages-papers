module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneGroundTypedIntroductionV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLiteralPriorTypedV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneRetypedGroundV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open NumberedWindowCheckerCoordinates (domain)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH requestedTypeTest)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open Paper16AccessibilityMilestoneGroundTypedIntroductionV2
  (exact_OriginalGroundTypedIntroduction exact_RequestedTypeTestFromResult)
open Paper16AccessibilityMilestoneLiteralPriorTypedV2 (priorTypedOf retypeWindow)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)

attribute [local irreducible] programGraph

/-- The reinstalled prior checker introduces ground typing from the carrier
and the result-field report at the same address. -/
theorem exact_RetypedGroundFromCarrierAndResult {S : Spine.Signature} {K : List Ty}
    (A : InstalledWindow S K (sourceWindow K)) (c : Nat) (ground : Ty.ground ∈ K)
    {α : Type} {Γ : List (Formula α)} (q : OTerm α)
    (held : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (carrier A.presentation false c q)))
    (result : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph rawResult z ![q]))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (typedAt (chosenH (retypeWindow A).probes (sourceWindow K)) .ground q)) := by
  let body := sourceBody A.presentation c
  have rawCarrier : Nonempty (Derivation body Γ (programGraph A.scalar (suc z) ![q])) :=
    (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      false c body α Γ q).mp held
  have lifted : Nonempty (Derivation body Γ (programGraph (domain A.scalar) (suc z) ![z, q])) := by
    unfold domain
    apply compositionValue A.scalar (fun _ => .projection (1 : Fin 2))
      (suc z) ![z, q] ![q] rawCarrier
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (1 : Fin 2) ![z, q]
  have request := exact_RequestedTypeTestFromResult z q result
  have prior : Nonempty (Derivation body Γ (programGraph (priorTypedOf A.scalar) (suc z) ![z, q])) := by
    rw [priorTypedOf, exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept (domain A.scalar) requestedTypeTest ![z, q] lifted request
  exact exact_OriginalGroundTypedIntroduction (retypeWindow A) c ground q prior result

#print axioms exact_RetypedGroundFromCarrierAndResult

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneRetypedGroundV2
