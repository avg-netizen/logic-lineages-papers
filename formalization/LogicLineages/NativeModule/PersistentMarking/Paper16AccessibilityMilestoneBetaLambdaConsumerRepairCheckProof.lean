module
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneBetaAddressProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLambdaClassifierProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneBetaLambdaConsumerRepairCheckProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowInternalProbeTargets (typeCode typedAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof (BetaJoinedRulesAt)
open NumberedWindowInternalLiteralAlignedBetaTargetProof (exact_OpenAlignedBetaRowRename)
open NumberedWindowInternalLiteralBetaLambdaClassifierProof (exact_OpenAcceptedBetaLambdaCases)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalNeutralFactsSyntaxProof (formulaRename)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow CarrierTypingCases)
open Paper16AccessibilityMilestoneBetaAddressProof
  (installedHop exact_OpenInstalledBetaRebuiltComputability)

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy} {α : Type}
variable {Γ : List (Formula α)}

/-- Apply the installed address rules inside the scopes created by
decoding a literal lambda and its successful child computation.
The remaining branch assumptions are the nonlambda case and the
computability of the specific rebuilt lambda instance. -/
theorem exact_OpenInstalledAlignedBetaLambdaComputability
    (A : InstalledWindow S K W) (c : Nat) (τ : Ty) (L₀ : Program 3)
    (V : Program 1) (H : Program 2) (U : Program 3) (typing : CarrierTypingCases A c)
    (joined : BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
      (installedHop A) L₀ A.least (zeroDepthInstance (singletonLambda V H U)) W A.probes c)
    {t ctx dom cod fn arg sc st after q r d e f a bind body y : OTerm α}
    (step : D (sourceBody A.presentation c) Γ (direct A.presentation (installedHop A) c t y))
    (row : AlignedBetaRow L₀ A.least (zeroDepthInstance (singletonLambda V H U)) (sourceBody A.presentation c) Γ
      ctx dom cod fn arg sc st after q r d e f a bind body y)
    (typeField : D (sourceBody A.presentation c) Γ (eqn st (numeral (typeCode (formulaType τ)))))
    (other : D (sourceBody A.presentation c) (unary rawLambdaShape z body :: Γ)
      (formula (applicationGuard A.scalar A.least) (formulaType τ) y))
    (instanceComputes : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (ty child value : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D (sourceBody A.presentation c) Δ (eqn (body.relabel j) (rawLambdaTerm ty child)) →
      D (sourceBody A.presentation c) Δ (programGraph U (suc value) ![a.relabel j,suc z,child]) →
      D (sourceBody A.presentation c) Δ
        (carrier A.presentation false c (addressTerm (sc.relabel j) (st.relabel j) (after.relabel j))) →
      D (sourceBody A.presentation c) Δ
        (typedAt (chosenH A.probes W) (formulaType τ)
          (addressTerm (sc.relabel j) (st.relabel j) (after.relabel j))) →
      D (sourceBody A.presentation c) Δ
        (programGraph A.least (suc (after.relabel j)) ![sc.relabel j,st.relabel j,rawLambdaTerm ty value]) →
      D (sourceBody A.presentation c) Δ
        (formula (applicationGuard A.scalar A.least) (formulaType τ)
          (addressTerm (sc.relabel j) (st.relabel j) (after.relabel j)))) :
    D (sourceBody A.presentation c) Γ (formula (applicationGuard A.scalar A.least) (formulaType τ) y) := by
  let B := sourceBody A.presentation c
  let p := applicationGuard A.scalar A.least
  let I := zeroDepthInstance (singletonLambda V H U)
  apply exact_OpenAcceptedBetaLambdaCases V H U a body r (formula p (formulaType τ) y) row.instanceRun other
  intro β j Δ ty child value keep shape run output
  have savedStep : D B Δ (direct A.presentation (installedHop A) c (t.relabel j) (y.relabel j)) := by
    simpa only [direct,edgeRename] using renameInto step j Δ keep
  have savedType : D B Δ (eqn (st.relabel j) (numeral (typeCode (formulaType τ)))) := by
    simpa only [eqnRelabel,numeralRename] using renameInto typeField j Δ keep
  have savedRow := exact_OpenAlignedBetaRowRename row j Δ keep
  rw [formulaRename]
  exact exact_OpenInstalledBetaRebuiltComputability A c τ L₀ I typing joined
    savedStep savedRow output savedType (instanceComputes β j Δ ty child value keep shape run)

#print axioms exact_OpenInstalledAlignedBetaLambdaComputability
end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneBetaLambdaConsumerRepairCheckProof
