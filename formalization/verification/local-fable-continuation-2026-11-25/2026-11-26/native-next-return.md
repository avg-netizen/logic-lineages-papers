**Finding:** the bridge is a mechanical port of 17 legacy files to the `NativeModule` prefix. Every dependency outside those 17 already exists on the native side or is a shared module file. I found no required body change in the four proof bodies I read; the other thirteen I checked by import lines only. Nothing here is compiled.

## Import identity, as checked

**Milestone's `fixed`.** Each step below is a `public import` line that I read:

1. `Paper16AccessibilityMilestoneTargets.lean:3` imports `NativeModule…ConditionalUpperUniformTargets`.
2. That file, line 3, imports `NativeModule…ConditionalMain16Targets`.
3. That file, line 3, imports `NativeModule…ConditionalUpperTargets`.
4. That file, line 5, imports `NativeModule…ConditionalUpperBridgeTargets`.
5. That file, line 4, imports `NativeModule…NumberedWindowArithmeticScalarTargets`, which defines `fixed` at line 16.

**`exact_OriginalValidWindow`'s `fixed`.** Each step is a plain `import` line in a file with no `module` header:

1. `…FreshProbeDispatchOriginalWindowChecks.lean:1` imports `…OriginalWindowTargets`.
2. That file, line 2, imports `NumberedWindowOriginalProbeTotalTargets`.
3. That file, line 2, imports `NumberedWindowOriginalComputabilityFormulaTargets`.
4. That file, line 2, imports `NumberedWindowApplicationGraphTargets`.
5. That file, line 1, imports `NumberedWindowAddressApplicationTargets`.
6. That file, line 2, imports the legacy `PersistentMarking.NumberedWindowArithmeticScalarTargets`, which defines `fixed` at line 12.

Both files use the namespace `LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets`, so the two declarations have the same full name and cannot be imported together.

## Port convention already used in the tree

Comparing the legacy and native `NumberedWindowActualPairAlgorithmChecks.lean`, the body is identical and only the header changes:

```lean
module

public import LogicLineages.NativeModule.PersistentMarking.<Dependency>

@[expose] public section

namespace LogicLineages.PersistentMarking.<SameNamespaceAsLegacy>
```

Shared module files keep their `LogicLineages.PersistentMarking.` path.

## The 17 files to create under `LogicLineages/NativeModule/PersistentMarking/`

Each is the legacy body with the header above. "N." means `LogicLineages.NativeModule.PersistentMarking.`, "P." means the shared `LogicLineages.PersistentMarking.` module file, and "new" marks a file from this list.

| # | File | `public import` lines |
|---|---|---|
| 1 | `NumberedWindowAddressApplicationTargets` | P.`NumberedWindowAddressApplication`; N.`NumberedWindowArithmeticScalarTargets`; N.`NumberedWindowExternalApplication`; N.`NumberedWindowPathWitnessTargets` |
| 2 | `NumberedWindowAddressApplicationClassProof` | N.#1 (new); N.`NumberedWindowArithmeticAllContextAdmittedProof`; N.`NumberedWindowArithmeticLeastClassChecks` |
| 3 | `NumberedWindowAddressApplicationDecodeProof` | N.#1 (new); N.`…ArithmeticScalarChecks`; N.`…ArithmeticAddressAlgorithmChecks`; N.`…ArithmeticFieldAlgorithmChecks`; N.`…ArithmeticClassAddressProof` |
| 4 | `NumberedWindowAddressApplicationChecks` | N.#3 (new); N.#2 (new) |
| 5 | `NumberedWindowApplicationGraphTargets` | N.#1 (new) |
| 6 | `NumberedWindowApplicationGraphProof` | N.#5 (new); N.#4 (new); N.`…ArithmeticAllContextAdmittedProof` |
| 7 | `NumberedWindowApplicationGraphChecks` | N.#6 (new) |
| 8 | `NumberedWindowFreeAddressTargets` | P.`NumberedWindowFreeAddress`; N.`…ExternalTypeFactsTargets`; N.`…ArithmeticAllContextBits`; N.`…PrimaryCoverSyntax` |
| 9 | `NumberedWindowFreeAddressProof` | N.#8 (new); N.`…ArithmeticFieldAlgorithmChecks`; N.`…ArithmeticAllContextAdmittedProof`; N.`…PathWitnessClassCode`; N.`…ExternalTypeFactsChecks`; N.`…ArithmeticCoverBoundsProof` |
| 10 | `NumberedWindowFreeAddressChecks` | N.#9 (new) |
| 11 | `NumberedWindowTypedProbeTargets` | P.`NumberedWindowTypedProbe`; N.#8 (new); N.#5 (new) |
| 12 | `NumberedWindowTypedProbeChecks` | N.#11 (new); N.#10 (new); N.#7 (new); N.`…ArithmeticScalarChecks`; N.`…ArithmeticAddressAlgorithmChecks`; N.`…ArithmeticAllContextAdmittedProof`; N.`…PathWitnessClassCode` |
| 13 | `NumberedWindowOriginalComputabilityFormulaTargets` | P.`NumberedWindowComputabilityReading`; N.#5 (new); N.`NumberedWindowExternalComputability` |
| 14 | `NumberedWindowOriginalProbeTotalTargets` | P.`NumberedWindowProbeCode`; N.#13 (new); N.#11 (new) |
| 15 | `NumberedWindowOriginalProbeTotalChecks` | N.#14 (new); N.#12 (new); N.`NumberedWindowActualPairAlgorithmChecks` |
| 16 | `NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets` | P.`NumberedWindowInternalFreshProbeDispatchWindowTargets`; N.#14 (new) |
| 17 | `NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks` | N.#16 (new); N.#15 (new); N.`…ArithmeticScalarChecks`; N.`…ArithmeticAddressAlgorithmChecks`; N.`…TypingBitsChecks`; N.`…ApplicationDomainProof` |

Evidence behind the table:

- **No native copy exists** for any of the 17. I globbed `NativeModule/PersistentMarking` for each family name.
- **Every "N." dependency not marked new exists** as a file there, and the ones whose headers I read have `@[expose] public section`.
- **Every "P." dependency is a `module` file with `@[expose] public section`**; I read all five headers.
- **The list is the closure of the legacy import lines**, which I read for every file in it.

I found no shorter route. `ValidWindow` needs `NumericalTotal`, whose legacy proof `exact_OriginalProbeTotal` goes through `exact_FreshProbeApplication`. That proof calls `exact_FreshArrowProbe` (files 8–10) and `exact_ClassApplicationGraph` (files 1–7).

## Body changes

I read the bodies of files 11, 12, 15 and 17 in full and file 16's statements. They unfold `typed`, `probe`, `code`, `formulaType` and `fixed` by `rw`, `simp` and `change`, and all of those definitions are in exposed sections. For the other twelve I checked only imports, so I cannot say their bodies port unchanged.

## The target, once the port exists

Append to the saved `Paper16AccessibilityMilestoneInstalledPacket.lean`, with one added import and open:

```lean
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks

open NumberedWindowInternalLiteralDirectCarrierInstalledProof (exact_ConcreteLiteralDirectCarrierTuple)

/-- The milestone selection target at the original source window. -/
theorem exact_SelectInstalledWindows : SelectInstalledWindows := by
  intro S K closed
  have valid :=
    NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks.exact_OriginalValidWindow S K closed
  obtain ⟨i,cv,tv,raw,L,p₀,v,packet⟩ :=
    exact_ConcreteLiteralDirectCarrierTuple S.entries (fixed S K) _ valid
  exact ⟨_,⟨installedOfPacket valid i cv tv raw L p₀ v packet⟩⟩

#print axioms exact_SelectInstalledWindows
```

The window is `sourceWindow K`, with its original definition `K.map formulaType`.

## Constraints to respect

- **Never import a ported file together with its legacy original.** They declare the same names, exactly as the existing native copies do.
- **Legacy files stay untouched.** Their current importers keep using them.
- **The saved packet module's own import risk is unchanged.** I searched only the `NumberedWindowInternal*` and `NumberedWindowFixed*` prefixes; there, three `PersistentMarking` files import the legacy `fixed` and must stay out of its closure.
