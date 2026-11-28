module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLiteralPriorTypedV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneOptionReinstallV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions

/-! Frozen targets for installing the literal probe leaves and for the resulting reduction of
`lem:arithmetic-accessibility` on one installed window per closed source universe
(Fable B, 27 November 2026).

`literalProbeWindow` stacks the three checked reinstallations of 26 November: the prior type
checker built from the installed scalar, the fresh selector reading the installed scalar, and the
binary option program built from the installed scalar and least program. The presentation
(scalar, multiset domain, path and direct checkers), the application guard and the least program
are unchanged.

`InstalledAccessibilityReduction` asserts neither `FreshApplicationTotal` nor
`TypedCarrierComputability`; it states that these two are what remains on the selected window. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes finiteScalar)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open Paper16AccessibilityMilestoneLiteralPriorTypedV2 (retypeWindow reinstallFreshScalar)
open Paper16AccessibilityMilestoneOptionReinstallV2 (reinstallOptionApplication)
open Paper16AccessibilityMilestoneTargetsV2
  (InstalledWindow CarrierTypingCases TypedCarrierComputability AllTerms)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2

/-- The same window with all three literal probe leaves installed. -/
def literalProbeWindow {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}
    (A : InstalledWindow S K W) : InstalledWindow S K W :=
  reinstallOptionApplication (reinstallFreshScalar (retypeWindow A))

/-- With the finite scalar filter over an address scalar, the installed application core, and
carriers of application results, the literal probe leaves supply all five open reports. -/
def StackedLiteralProbeReports : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (A : InstalledWindow S K (sourceWindow K))
    (forming : Program 3),
    A.scalar = finiteScalar (addressScalar A.contextGuard A.typeGuard forming A.least)
      (finiteCodes (sourceWindow K)) →
    A.application = applicationCore A.least →
    ∀ c : Nat, ApplicationResultCarrier A c → LiteralProbeReports (literalProbeWindow A) c

/-- For every closed source universe there is one installed window on which the type split
follows from the fresh application, and the internal all-terms sentence follows from the type
split and typed carrier computability alone. -/
def InstalledAccessibilityReduction : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ A : InstalledWindow S K (sourceWindow K), ∀ c : Nat,
      (FreshApplicationTotal A c → CarrierTypingCases A c) ∧
      (CarrierTypingCases A c → TypedCarrierComputability A c → AllTerms A c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2
