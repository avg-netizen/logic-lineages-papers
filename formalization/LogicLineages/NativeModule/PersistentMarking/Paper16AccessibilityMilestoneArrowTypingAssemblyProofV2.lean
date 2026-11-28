module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallProofV2
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFreshNeutralBridgeProof

/-! Proof of the frozen
`Paper16AccessibilityMilestoneArrowTypingAssemblyTargetsV2.WindowReductionFromJoinedFacts`
(Fable B, 27 November 2026).

First part: the five probe reports of the stacked window and the reduction of the type split.
Second part: the assembly of `exact_CloseAllTerms`, with the computability-to-membership step
taken from `exact_TupleComputabilityToIFromArithmetic` on the reinstalled tuple. That step
rebuilds typed-probe totality, the given-fresh alignment and fresh-variable computability from the
tuple itself, the neutral arithmetic and the forward rule. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRules (carrier membership)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralFreshNeutralBridgeProof (exact_TupleComputabilityToIFromArithmetic)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2 (literalProbeWindow)
open Paper16AccessibilityMilestoneArrowTypingAssemblyTargetsV2
open Paper16AccessibilityMilestoneArrowTypingProofV2 (exact_TypingCasesFromReports)
open Paper16AccessibilityMilestoneArrowTypingInstallProofV2 (exact_StackedLiteralProbeReports)

/-- The reduction of the type split and of the all-terms sentence on the window with literal
probe leaves. -/
theorem exact_WindowReductionFromJoinedFacts : WindowReductionFromJoinedFacts := by
  intro S K A forming step neutral bottom shape core c output arithmetic forward
  let B := literalProbeWindow A
  refine ⟨?_, ?_⟩
  · intro total
    exact exact_TypingCasesFromReports B c
      (exact_StackedLiteralProbeReports S K A forming shape core c output) total
  · intro typing computed
    let q : OTerm (Empty ⊕ Fin 1) := .var (.inr 0)
    let body := sourceBody B.presentation c
    let domain := carrier B.presentation false c q
    let goal := membership false q
    have domainHyp : Nonempty (Derivation body [domain] domain) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have result : Nonempty (Derivation body [domain] goal) := by
      apply typing (Empty ⊕ Fin 1) [domain] q goal domainHyp
      intro τ hτ
      let typed := typedAt (chosenH B.probes (sourceWindow K)) (formulaType τ) q
      let Γ := [typed, domain]
      have typedHyp : Nonempty (Derivation body Γ typed) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have heldDomain : Nonempty (Derivation body Γ domain) :=
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      exact exact_TupleComputabilityToIFromArithmetic S.entries (fixed S K) (sourceWindow K)
        B.scalar (jRaw B.scalar) B.path (dCore B.scalar B.path permutation) B.probes c
        step neutral bottom B.installed.1 arithmetic forward
        (formulaType τ) (Empty ⊕ Fin 1) Γ q typedHyp (computed τ hτ _ Γ q heldDomain typedHyp)
    obtain ⟨proof⟩ := result
    exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction proof)⟩

#print axioms exact_WindowReductionFromJoinedFacts

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2
