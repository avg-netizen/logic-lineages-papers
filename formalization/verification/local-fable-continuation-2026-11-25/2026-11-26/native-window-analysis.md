**Finding:** there are no selected windows yet to re-point at a new `U`. The milestone structure does support the installation, and a short construction shows the program identities are retained. One selection theorem is still missing. Nothing here is compiled.

## What the milestone actually contains

- **`InstalledWindow` is never constructed.** `InstalledWindow`, `SelectInstalledWindows`, `CloseAllTerms` and `TypedCarrierComputability` occur in exactly one file, `Paper16AccessibilityMilestoneTargets.lean`. What exists downstream is the existential `Packet` (`…LiteralDirectCarrierInstalledProof.lean:58`).
- **`InstalledTupleAt` does not mention `U`.** It is four conjuncts (`…SparseTupleDefinitions.lean:54`): `TupleAt`, the application-guard equation, `CallbacksAt` (closed numeric calibrations of `cv`, `tv`, `raw`, `least`) and `InstalledReportAt`. `raw` is an opaque `Program 5`.
- **Consequence.** An `InstalledWindow` has no field recording that its `raw` contains `withBetaLeaf Va U leaves`. A bare `Nonempty (InstalledWindow S K W)`, which is what `SelectInstalledWindows` states, forgets which `U` was installed.

## Does parametrising the packet carry `U` into a window?

Yes, structurally, as long as the window is returned in the same existential as its rules.

- `Packet.physical` has exactly the type of the `installed` field, with `scalar := i`, `contextGuard := cv`, `typeGuard := tv`, `least := L`, `application := p₀`, `probes := v`. Its `Raw` is an abbreviation of `rawWithTarget`.
- `S i cv tv R L` is an abbreviation of `literalData i (addressPositive cv tv R L)` (`…AddressedChildReportsProof.lean:57`). That is what `InstalledWindow.presentation` unfolds to, so `BetaJoinedRulesAt` is already stated at the window's own presentation.

The construction below is the source-exact check of both points.

Suggested file: `LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneInstalledPacket.lean`

```lean
module
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectCarrierInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildReportsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneInstalledPacket

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open Paper16AccessibilityMilestoneTargets

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

/-- A physical packet at the fixed settings of a source window is an
installed window with the same seven programs. -/
def installedOfPacket (valid : ValidWindow (fixed S K) W) (i cv tv : Program 1)
    (raw : Program 5) (L p₀ : Program 3) (v : Inputs)
    (packet : Packet S.entries (fixed S K) W i cv tv raw L p₀ v) : InstalledWindow S K W :=
  ⟨valid,i,cv,tv,raw,L,p₀,v,packet.physical⟩

/-- Its presentation is the packet's own source data, so every rule
proved at that data is a rule of the window. -/
theorem installedOfPacket_presentation (valid : ValidWindow (fixed S K) W) (i cv tv : Program 1)
    (raw : Program 5) (L p₀ : Program 3) (v : Inputs)
    (packet : Packet S.entries (fixed S K) W i cv tv raw L p₀ v) :
    (installedOfPacket valid i cv tv raw L p₀ v packet).presentation =
      NumberedWindowInternalLiteralAddressedChildReportsProof.S i cv tv
        (rawWithTarget i cv tv raw L) L := rfl

#print axioms installedOfPacket
#print axioms installedOfPacket_presentation
end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneInstalledPacket
```

I copied `Spine.Signature` and `Ty` from the milestone's `variable` line and did not check which of its opens resolves them. If either fails to resolve, copy the milestone's open block.

## The missing selection theorem

For each signature `S` and closed `K`, and each `U` with `InstanceFit U`, it must produce, in one existential:

- a window `A : InstalledWindow S K (sourceWindow K)`;
- the equation for `A.raw` exhibiting `withBetaLeaf Va U leaves` inside `guardedRaw (strictDualRaw …)`;
- `BetaJoinedRulesAt A.presentation … U … c` for every `c`.

Its proof would be the `U`-parametrised `exact_ConcreteLambdaJoinedRules` at `xs := S.entries`, `s := fixed S K`, followed by `installedOfPacket`. That needs the five packet premises at `fixed S K`:

| Premise | Status |
|---|---|
| `ValidWindow (fixed S K) (sourceWindow K)` | found: `exact_OriginalValidWindow` (`…FreshProbeDispatchOriginalWindowChecks.lean:64`) |
| `WindowSeedsCovered (fixed S K)` | found: `exact_FixedWindowSeedsCovered` (`NumberedWindowOriginalFixedSeedCoverageProof.lean:12`) |
| `HeadPairsSymmetric (fixed S K).equivalentHeads` | not located |
| `GrammarTypeInclusion (fixed S K)` | not located |
| `included` for `finiteCodes (sourceWindow K)` | not located |

"Not located" means my searches did not find them; it is not a claim that they are absent.

## Check of the earlier bridges against the sources

- **`exact_OpenAlignedBetaRowLambdaBoundAbove`.** `AlignedBetaRow` takes `(L₀ L : Program 3) (U : Program 2) (B) {α} (Γ)` and then seventeen terms in the order `ctx dom cod fn arg sc st after q r d e f a bind body y`; my application matches. The call into `exact_OpenBetaLambdaBoundAboveTarget` matches the saved order `V H W a body ty t i r goal inserted lambdaNode boundNode shape above held use`. The row's `D` and the theorem's `D` are both abbreviations of `Nonempty (Derivation B Γ f)`, so `row.instanceRun` is acceptable as `held`.
- **`exact_PhysicalSingletonLambdaBetaInstallation`.** The argument orders of `exact_LiteralBetaLeafFit`, `exact_ZeroDepthInstance` and `exact_LiteralSingletonLambdaCalibrationOfGuarded` match the sources. Its `fixed` is `NumberedWindowRootDispatchAlgorithm.fixed`, a different function from the milestone's `fixed`.
- **Packet parametrisation.** `U` appears in the packet proof only in the leaf definition, the `exact_LiteralBetaLeafFit` call and the witness tuple; the edit list from last round stands.

One cost I had not flagged: the row bridge imports `…BetaOperandAlignmentProof`, which pulls the enriched-edge and addressed-beta closure into the singleton lane.
