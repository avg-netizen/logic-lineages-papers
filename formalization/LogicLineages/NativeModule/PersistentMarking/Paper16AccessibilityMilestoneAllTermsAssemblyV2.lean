module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneAllTermsAssemblyV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRules (carrier membership)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (chosenA chosenH)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalProbeTargets (typedAt)
open NumberedWindowInternalProbeChecks (exact_TypedComputabilityImpliesMembership)
open NumberedWindowInternalPullbackChecks (exact_InternalPullback)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneTargetsV2 (CloseAllTerms InstalledWindow)

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

/-- Assemble the internal scalar sentence in the given installed presentation
using its finite typing cases, application rules, and typed computability. -/
theorem exact_CloseAllTerms (A : InstalledWindow S K W) (c : Nat) : CloseAllTerms A c := by
  intro typingCases arithmetic computed
  have tuple := A.installed.1
  obtain ⟨_, _, _, _, _, guards, _⟩ := tuple
  have pullback :=
    exact_InternalPullback A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      A.probes.applicationGuard c guards arithmetic.forwardEdge
  let q : OrdinaryArithmetic.Term (Empty ⊕ Fin 1) := .var (.inr 0)
  let body := sourceBody A.presentation c
  let domain := carrier A.presentation false c q
  let goal := membership false q
  have domainHyp : Nonempty (Derivation body [domain] domain) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result : Nonempty (Derivation body [domain] goal) := by
    apply typingCases (Empty ⊕ Fin 1) [domain] q goal domainHyp
    intro τ hτ
    let typed := typedAt (chosenH A.probes W) (formulaType τ) q
    let Γ := [typed, domain]
    have typedHyp : Nonempty (Derivation body Γ typed) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have heldDomain : Nonempty (Derivation body Γ domain) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    exact exact_TypedComputabilityImpliesMembership A.presentation A.probes.applicationGuard
      (chosenH A.probes W) (chosenA A.probes) c pullback arithmetic.typedProbe arithmetic.freshComputable
      (formulaType τ) (Empty ⊕ Fin 1) Γ q typedHyp (computed τ hτ _ Γ q heldDomain typedHyp)
  obtain ⟨proof⟩ := result
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction proof)⟩

#print axioms exact_CloseAllTerms

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneAllTermsAssemblyV2
