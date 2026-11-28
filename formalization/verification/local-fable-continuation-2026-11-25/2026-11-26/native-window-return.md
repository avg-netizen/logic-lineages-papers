The construction and the same-window rules package fit in one small module. Nothing here is compiled. The generic theorem takes any `U`, so it needs no change when the packet is later parametrised.

Suggested file: `LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneInstalledPacket.lean`

```lean
module
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteLambdaJoinedRulesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectCarrierInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildReportsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneInstalledPacket

-- The milestone's own open block, so that its binder types resolve identically.
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
-- Additional names used here.
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard applicationCore)
open NumberedWindowInternalLiteralAddressedChildReportsProof (hop)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit)
open NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof
  (BetaJoinedRulesAt exact_ConcreteBetaJoinedRules)
open NumberedWindowInternalLiteralConcreteLambdaJoinedRulesProof (exact_ConcreteLambdaJoinedRules)
open Paper16AccessibilityMilestoneTargets

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

/-- A physical packet at the fixed settings of `S K` on the probe list `W`
is an installed window with the same seven programs and probe inputs. -/
def installedOfPacket (valid : ValidWindow (fixed S K) W) (i cv tv : Program 1)
    (raw : Program 5) (L p₀ : Program 3) (v : Inputs)
    (packet : Packet S.entries (fixed S K) W i cv tv raw L p₀ v) : InstalledWindow S K W :=
  ⟨valid,i,cv,tv,raw,L,p₀,v,packet.physical⟩

/-- One window together with the joined beta rules on its own presentation,
its own scalar, least program and probe inputs. The instance program `U`
and the unguarded least `L₀` are part of the same package. -/
def JoinedBetaWindow (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) : Prop :=
  ∃ (A : InstalledWindow S K W) (U : Program 2) (L₀ : Program 3),
    InstanceFit U ∧
    A.application = applicationCore A.least ∧
    A.probes.applicationGuard = applicationGuard A.scalar A.least ∧
    ∀ c : Nat, BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
      (hop A.contextGuard A.typeGuard
        (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
      L₀ A.least U W A.probes c

/-- Packaging. Any packet with joined beta rules at its own source data
gives the package; every component is the packet's own, by unfolding. -/
theorem exact_JoinedBetaWindowOfPacket (valid : ValidWindow (fixed S K) W)
    (i cv tv : Program 1) (U : Program 2) (raw : Program 5) (L₀ L : Program 3) (placed : Inputs)
    (fit : InstanceFit U)
    (packet : Packet S.entries (fixed S K) W i cv tv raw L (applicationCore L) placed)
    (placedApp : placed.applicationGuard = applicationGuard i L)
    (rules : ∀ c : Nat, BetaJoinedRulesAt
      (NumberedWindowInternalLiteralAddressedChildReportsProof.S i cv tv
        (rawWithTarget i cv tv raw L) L)
      i (applicationGuard i L) (hop cv tv (rawWithTarget i cv tv raw L) L) L₀ L U W placed c) :
    JoinedBetaWindow S K W := by
  unfold JoinedBetaWindow
  exact ⟨installedOfPacket valid i cv tv raw L (applicationCore L) placed packet,U,L₀,
    fit,rfl,placedApp,rules⟩

/-- The checked beta packet as a window package. -/
theorem exact_JoinedBetaWindow (valid : ValidWindow (fixed S K) W)
    (seeds : WindowSeedsCovered (fixed S K))
    (symmetric : HeadPairsSymmetric (fixed S K).equivalentHeads)
    (grammar : GrammarTypeInclusion (fixed S K))
    (included : ∀ t ∈ finiteCodes W, t ∈ (fixed S K).window.1) :
    JoinedBetaWindow S K W := by
  obtain ⟨i,cv,tv,U,raw,L₀,L,placed,fit,packet,placedApp,rules⟩ :=
    exact_ConcreteBetaJoinedRules S.entries (fixed S K) W valid seeds symmetric grammar included
  exact exact_JoinedBetaWindowOfPacket valid i cv tv U raw L₀ L placed fit packet placedApp rules

/-- The checked packet with the contextual lambda fallback as a window package. -/
theorem exact_JoinedLambdaWindow (valid : ValidWindow (fixed S K) W)
    (seeds : WindowSeedsCovered (fixed S K))
    (symmetric : HeadPairsSymmetric (fixed S K).equivalentHeads)
    (grammar : GrammarTypeInclusion (fixed S K))
    (included : ∀ t ∈ finiteCodes W, t ∈ (fixed S K).window.1) :
    JoinedBetaWindow S K W := by
  obtain ⟨cv,tv,U,X,base,T,V,baseM,leaves,other₀,placed,fit,packet,placedApp,rules⟩ :=
    exact_ConcreteLambdaJoinedRules S.entries (fixed S K) W valid seeds symmetric grammar included
  exact exact_JoinedBetaWindowOfPacket valid _ cv tv U _ _ _ placed fit packet placedApp rules

#print axioms installedOfPacket
#print axioms exact_JoinedBetaWindowOfPacket
#print axioms exact_JoinedBetaWindow
#print axioms exact_JoinedLambdaWindow
end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneInstalledPacket
```

## Why the identities are preserved

- **`installed` field.** `Packet.physical` (`…LiteralDirectCarrierInstalledProof.lean:60-62`) has the type of `InstalledWindow.installed` under `scalar := i`, `contextGuard := cv`, `typeGuard := tv`, `least := L`, `application := p₀`, `probes := v`. Both sides use the same `jRaw`, `dCore`, `permutation` and `rawWithTarget`.
- **Presentation.** `S i cv tv R L` abbreviates `literalData i (addressPositive cv tv R L)` (`…AddressedChildReportsProof.lean:57`), which is what `A.presentation` unfolds to. That is why `rules` can be passed unchanged.
- **Same window.** Every argument of `BetaJoinedRulesAt` in the package is a projection of `A`, apart from `U` and `L₀`, which sit in the same existential.

## Source assumptions

- **`S`, `K`, `W` are arbitrary.** The construction forces `xs := S.entries` and `s := fixed S K`, with `fixed` from `NumberedWindowArithmeticScalarTargets`, because that is what the `installed` field states. `Closed K` is not used here.
- **Probe legality is `valid : ValidWindow (fixed S K) W`.** It becomes the window's own `valid` field. For `W := sourceWindow K` with `Closed K` it is `exact_OriginalValidWindow` (`…FreshProbeDispatchOriginalWindowChecks.lean:64`).
- **Probe inputs.** `A.probes` is the packet's `placed`. Its application-guard equation is a package component, and `TupleAt` with the guard equation of `InstalledTupleAt` stays inside `A.installed`.
- **Four settings premises** are the hypotheses of the two concrete rules theorems, at `fixed S K`:
  - `seeds` has the statement shape of `exact_FixedWindowSeedsCovered` (`NumberedWindowOriginalFixedSeedCoverageProof.lean:12`). I did not confirm that it uses the same `fixed`.
  - `symmetric`, `grammar` and `included` I did not locate at `fixed S K`.
- **`U` in the two corollaries** is still the abstract program from `exact_LiteralSingletonInstance`, with only the closed numeric `InstanceFit U`. A physical `U` enters through `exact_JoinedBetaWindowOfPacket` once the rules theorem is parametrised.

## Unverified points

- **Import compatibility.** The module joins the milestone's `NativeModule` closure with the joined-rules closure. Some modules exist in both trees under the same namespace. I checked only that the `Conditional…Targets` files have no non-native duplicate; a clash elsewhere in the closures is possible.
- **Name resolution.** `Spine.Signature` and `Ty` are written as in the milestone, which is why its open block is copied.
- **Definitional steps.** The `rfl` component and the unchanged `rules` rely on unfolding `installedOfPacket`, `InstalledWindow.path` and `InstalledWindow.presentation`.
- **Lambda corollary.** The four `_` arguments are meant to be solved from the types of `packet` and `rules`; the `obtain` pattern follows the order of the existential at `…ConcreteLambdaJoinedRulesProof.lean:97-98`.
