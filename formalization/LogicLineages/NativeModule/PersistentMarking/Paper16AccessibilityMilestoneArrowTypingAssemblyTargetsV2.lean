module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions

/-! Frozen target for the assembly of `lem:arithmetic-accessibility` on a window with literal
probe leaves, from the facts that the joined rules of 26 November provide
(Fable B, 27 November 2026).

The hypotheses are stated on the original window `A` and do not mention its probe leaves beyond
the application guard, which the reinstallation keeps: the finite scalar shape, the application
core, carriers of application results, the neutral arithmetic package, and the forward rule.
The conclusion is on `literalProbeWindow A`. The four-field `ApplicationArithmetic` premise of
`CloseAllTerms` (including backward matching) does not occur. Neither `FreshApplicationTotal` nor
`TypedCarrierComputability` is asserted. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyTargetsV2

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalAtomicRefinement (freeSource)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes finiteScalar)
open NumberedWindowInternalNeutralFactsTargets (Arithmetic)
open NumberedWindowInternalPullbackTargets (ForwardRule)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open Paper16AccessibilityMilestoneTargetsV2
  (InstalledWindow CarrierTypingCases TypedCarrierComputability AllTerms)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2
open Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2 (literalProbeWindow)

/-- On the window with literal probe leaves, the type split follows from the fresh application,
and the all-terms sentence from the type split and typed carrier computability. -/
def WindowReductionFromJoinedFacts : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (A : InstalledWindow S K (sourceWindow K))
    (forming step : Program 3) (neutral bottom : Program 1),
    A.scalar = finiteScalar (addressScalar A.contextGuard A.typeGuard forming A.least)
      (finiteCodes (sourceWindow K)) →
    A.application = applicationCore A.least →
    ∀ c : Nat,
      ApplicationResultCarrier A c →
      Arithmetic A.presentation A.probes.applicationGuard step neutral bottom freeSource c →
      ForwardRule A.presentation A.probes.applicationGuard c →
      (FreshApplicationTotal (literalProbeWindow A) c →
        CarrierTypingCases (literalProbeWindow A) c) ∧
      (CarrierTypingCases (literalProbeWindow A) c →
        TypedCarrierComputability (literalProbeWindow A) c → AllTerms (literalProbeWindow A) c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyTargetsV2
