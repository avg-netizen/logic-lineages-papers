module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneApplicationResultTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneBetaAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInheritedApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

/-! Proof of the frozen
`Paper16AccessibilityMilestoneApplicationResultTargetsV2.ApplicationResultTyped`
(Fable B3, 27 November 2026). Composition of accepted laws:

1. the result is a scalar carrier (`applicationOutput` of the joined rules);
2. the acceptance opens to the parsed operands and the emitted address
   `t = addressTerm ctx cod k` (`exact_OpenLiteralApplicationRows`);
3. the parsed codomain is the literal code of `τ`
   (`exact_OpenInstalledBetaApplicationTypeField` at `st := cod`);
4. the result field of the literal address is `cod` (`literalAddress`), moved to `t` along the
   emitted equation (`headTransport`);
5. the type split selects the requested type (`exact_OpenInstalledCarrierRequestedType`). -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneApplicationResultProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalProbeTargets (typedAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (typedRename)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalLiteralApplicationRowsProof (exact_OpenLiteralApplicationRows)
open NumberedWindowInternalLiteralInheritedApplicationProof (exact_OriginalApplicationAcceptedGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow CarrierTypingCases)
open Paper16AccessibilityMilestoneBetaAddressProof
  (exact_OpenInstalledBetaApplicationTypeField exact_OpenInstalledCarrierRequestedType)
open Paper16AccessibilityMilestoneTypedRowsTargetsV2 (windowApp JoinedAt)
open Paper16AccessibilityMilestoneApplicationResultTargetsV2

theorem exact_ApplicationResultTyped : ApplicationResultTyped := by
  intro S K W A L₀ U c typing joined σ τ α Γ x u t typed app
  let B := sourceBody A.presentation c
  obtain ⟨held, _⟩ := joined.applicationOutput α Γ x u t app
  have graph : D B Γ (programGraph (applicationGuard A.scalar A.least) (suc z) ![x, u, t]) := by
    rw [← exact_OriginalApplicationAcceptedGraph]
    exact app
  apply exact_OpenLiteralApplicationRows A.scalar A.least x u t
    (typedAt (chosenH A.probes W) (formulaType τ) t) graph
  intro β j Δ ctx result dom cod fn arg atResult keep _ _ parsed _ emitted
  rw [typedRename]
  have typed' : D B Δ
      (typedAt (chosenH A.probes W) (formulaType (.arrow σ τ)) (x.relabel j)) := by
    simpa only [typedRename] using renameInto typed j Δ keep
  have held' : D B Δ (carrier A.presentation false c (t.relabel j)) := by
    simpa only [carrierRename] using renameInto held j Δ keep
  have codeEq := exact_OpenInstalledBetaApplicationTypeField A c σ τ (x.relabel j)
    (u.relabel j) ctx result dom cod fn arg cod typed' parsed ⟨refl cod⟩
  obtain ⟨emitted⟩ := emitted
  have literal : D B Δ (programGraph rawResult cod ![addressTerm ctx cod atResult]) :=
    (literalAddress (body := B) (Γ := Δ) ctx cod atResult).2.2.1
  have reported : D B Δ (programGraph rawResult cod ![t.relabel j]) :=
    headTransport rawResult cod (addressTerm ctx cod atResult) (t.relabel j) ![]
      ⟨symm emitted⟩ literal
  exact exact_OpenInstalledCarrierRequestedType A c typing τ (t.relabel j) cod held' reported
    codeEq

#print axioms exact_ApplicationResultTyped

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneApplicationResultProofV2
