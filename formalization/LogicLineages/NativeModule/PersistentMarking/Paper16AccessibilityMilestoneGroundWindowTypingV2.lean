module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneRetypedGroundV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneGroundWindowTypingV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (typedRename)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipSupportProof (memberToChoices)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open Paper16AccessibilityMilestoneLiteralPriorTypedV2 (retypeWindow)
open Paper16AccessibilityMilestoneRetypedGroundV2 (exact_RetypedGroundFromCarrierAndResult)
open Paper16AccessibilityMilestoneTargetsV2 (CarrierTypingCases InstalledWindow)

attribute [local irreducible] programGraph

/-- On the original singleton ground window, the literal scalar filter forces
the result-field report to code zero and supplies the open ground typing. -/
theorem exact_RetypedGroundFromFiniteScalar {S : Spine.Signature}
    (A : InstalledWindow S [Ty.ground] (sourceWindow [Ty.ground])) (c : Nat)
    (base : Program 1) (shape : A.scalar = finiteScalar base [0])
    {α : Type} {Γ : List (Formula α)} (q : OTerm α)
    (held : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (carrier A.presentation false c q))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (typedAt (chosenH (retypeWindow A).probes (sourceWindow [Ty.ground])) .ground q)) := by
  let body := sourceBody A.presentation c
  let h := chosenH (retypeWindow A).probes (sourceWindow [Ty.ground])
  apply programCases rawResult ![q] (typedAt h .ground q)
  intro β j Δ ty includes reported
  rw [typedRename]
  have held' := renameInto held j Δ includes
  rw [carrierRename] at held'
  have accepted : Nonempty (Derivation body Δ (programGraph A.scalar (suc z) ![q.relabel j])) :=
    (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      false c body β Δ (q.relabel j)).mp held'
  rw [shape] at accepted
  have inputs : (fun i : Fin 1 => (![q] i).relabel j) = ![q.relabel j] := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [inputs] at reported
  have listed := (exact_OpenLiteralFiniteScalar base [0] (q.relabel j) ty reported accepted).2
  obtain ⟨choices⟩ := memberToChoices [0] ty listed
  have equal : Nonempty (Derivation body Δ (eqn ty z)) :=
    ⟨disjunctionElimination choices
      (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
      (Derivation.implicationIntroduction (Derivation.explosion (Derivation.hypothesis List.mem_cons_self)))⟩
  have groundResult := outputTransport rawResult ty z ![q.relabel j] equal reported
  exact exact_RetypedGroundFromCarrierAndResult A c List.mem_cons_self
    (q.relabel j) held' groundResult

theorem exact_RetypedCarrierTypingCasesGround {S : Spine.Signature}
    (A : InstalledWindow S [Ty.ground] (sourceWindow [Ty.ground])) (c : Nat)
    (base : Program 1) (shape : A.scalar = finiteScalar base [0]) :
    CarrierTypingCases (retypeWindow A) c := by
  intro α Γ q goal held branches
  obtain ⟨typed⟩ := exact_RetypedGroundFromFiniteScalar A c base shape q held
  obtain ⟨branch⟩ := branches Ty.ground List.mem_cons_self
  exact ⟨Derivation.implicationElimination (Derivation.implicationIntroduction branch) typed⟩

#print axioms exact_RetypedGroundFromFiniteScalar
#print axioms exact_RetypedCarrierTypingCasesGround

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneGroundWindowTypingV2
