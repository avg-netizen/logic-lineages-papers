**Finding:** `SelectInstalledWindows` does not follow from any proven theorem that can be imported next to the milestone. The smallest missing theorem is a valid-window existence statement for the milestone's own `fixed`. The proven one, `exact_OriginalValidWindow`, is about a different declaration of `fixed`. Nothing here is compiled.

## What the target actually needs

`SelectInstalledWindows` only asks for some `W` and some `InstalledWindow S K W`. That needs a packet, not the joined rules, and the weakest packet theorem takes only probe legality:

- `exact_ConcreteLiteralDirectCarrierTuple` (`…LiteralDirectCarrierInstalledProof.lean:83`) takes `valid : ValidWindow s W` and nothing else.
- So `JoinedLambdaWindow` is not on the shortest path. Its four extra premises (`seeds`, `symmetric`, `grammar`, `included`) matter only for a window that also carries the rules.

The exact missing theorem is therefore:

```lean
∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
  ∃ W : List ProbeTy, ValidWindow (fixed S K) W
```

with `fixed` the declaration the milestone sees.

## Why the proven theorem does not supply it

There are two declarations named `LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets.fixed`:

- a legacy one in `LogicLineages/PersistentMarking/NumberedWindowArithmeticScalarTargets.lean:12` (no `module` header, legacy imports);
- a second one in `LogicLineages/NativeModule/PersistentMarking/NumberedWindowArithmeticScalarTargets.lean:16` (`module`, `NativeModule` imports).

The bodies are textually identical, but they are separate declarations with the same name, so the two files cannot be imported into one environment.

- **The milestone is on the `NativeModule` side.** Every import of that file inside `NativeModule/` is the `NativeModule` copy, and the milestone reaches `fixed` through `ConditionalUpperUniformTargets`. I did not trace that chain to the end.
- **`exact_OriginalValidWindow` is on the legacy side.** It lives in `…FreshProbeDispatchOriginalWindowChecks.lean:64`, a legacy file whose `fixed` is the legacy one.
- **`sourceWindow` is legacy-only.** In `NativeModule/`, `ValidWindow` occurs only in the milestone and in the saved packet module, and no `sourceWindow K` occurs anywhere there.

## The exact dependency

A `NativeModule`-side version of `exact_OriginalValidWindow`. Its legacy proof is three components (`…OriginalWindowChecks.lean:28-66`):

| Component | Legacy suppliers | `NativeModule` copy of supplier |
|---|---|---|
| `TypeSupport (fixed S K) (sourceWindow K)` | `exact_ScalarAddress`, `exact_ExactAddressView`, `exact_FiniteWindowBit`, `rootInWindow`, `exact_FormulaTypeCoding` | first four exist (`…ArithmeticScalarChecks`, `…ArithmeticAddressAlgorithmChecks`, `…TypingBitsChecks`, `…ApplicationDomainProof`); the last does not |
| `ChildClosed (sourceWindow K)` | `arrowRight`, `subtypeSelf` | exists (`…ApplicationDomainProof`) |
| `NumericalTotal …` | `exact_OriginalProbeTotal` | no copy of `NumberedWindowOriginalProbeTotalChecks` |

So the files without a `NativeModule` counterpart are:

- `NumberedWindowOriginalComputabilityFormulaTargets` (for `formulaType`),
- `NumberedWindowOriginalProbeTotalTargets` and `…Checks`,
- `NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets` and `…Checks`.

`…OriginalProbeTotalChecks` also imports `NumberedWindowTypedProbeChecks` and `NumberedWindowActualPairAlgorithmChecks`; I did not check whether those have copies.

## Reduction of the target to that one hypothesis

This can be appended to the saved `Paper16AccessibilityMilestoneInstalledPacket.lean`. It needs one more open line:

```lean
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (exact_ConcreteLiteralDirectCarrierTuple)

/-- The milestone selection target, with its original quantifiers, from
probe legality at the fixed settings alone. -/
theorem exact_SelectInstalledWindowsOfValid
    (validWindows : ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
      ∃ W : List ProbeTy, ValidWindow (fixed S K) W) :
    SelectInstalledWindows := by
  intro S K closed
  obtain ⟨W,valid⟩ := validWindows S K closed
  obtain ⟨i,cv,tv,raw,L,p₀,v,packet⟩ :=
    exact_ConcreteLiteralDirectCarrierTuple S.entries (fixed S K) W valid
  exact ⟨W,⟨installedOfPacket valid i cv tv raw L p₀ v packet⟩⟩

#print axioms exact_SelectInstalledWindowsOfValid
```

## The other four premises, for the window with rules

| Premise at `fixed S K` | Legacy side | `NativeModule` side |
|---|---|---|
| `seeds` | `exact_FixedWindowSeedsCovered` (`NumberedWindowOriginalFixedSeedCoverageProof.lean:12`) | not found |
| `grammar` | `exact_FixedGrammarTypeInclusion` (`NumberedWindowFixedGrammarTypeInclusionOnly.lean:14`, a four-line list argument) | not searched |
| `symmetric` | not located | not located |
| `included` | not located; the ingredients are `exact_FormulaTypeCoding` and subtype closure of `K` | not located |

`included` is a real constraint, not bookkeeping: the window's type list is `K` filtered by `typesIn K (subtypes σ)` (`NativeModule/…/NumberedWindowAdmissionTargets.lean:19`), so every code of `sourceWindow K` must pass that filter.

## A risk for the saved packet module

The same name clash can break its imports. Three `PersistentMarking` files import the legacy `fixed`: `NumberedWindowInternalFreshProbeDispatchOriginalIntegrationTargets`, `NumberedWindowFixedGrammarTypeInclusionOnly` and `NumberedWindowFixedGrammarTypeTargets`. If any of them is in the closure of `…ConcreteLambdaJoinedRulesProof`, the saved module cannot be imported together with the milestone. I searched only files with the `NumberedWindowInternal` and `NumberedWindowFixed` prefixes for this.
