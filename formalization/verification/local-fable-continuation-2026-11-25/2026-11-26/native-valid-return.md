**Finding:** no shortcut exists. An empty or singleton probe list does not inhabit `ValidWindow`, and no native theorem supplies the heavy conjunct, so the port is necessary. Comparing native copies against their legacy originals, I found nothing likely to break it.

## Why an explicit small window does not work

`ValidWindow s W` is `TypeSupport s W ∧ ChildClosed W ∧ NumericalTotal (typed s) (probe s) (graph s)` (`…FreshProbeDispatchWindowTargets.lean:24`).

- **The third conjunct does not mention `W`.** `NumericalTotal` (`NumberedWindowProbeCode.lean:11`) says every arrow-typed address has a defined probe, an application result, and a typed result. No choice of `W` removes it.
- **`W := []` fails the first conjunct in general.** `TypeSupport s []` is the statement that `typed s t q` is never true. The legacy `exact_TypedAddress` (`NumberedWindowTypedProbeChecks.lean:23`) shows `typed (fixed S K) (encodeTy τ) n` holds exactly when `n` is the address of a coded class. `existsCode` gives a code to every class. So it fails as soon as any class exists.
- **A singleton fails the same way** once classes exist at two different types.

I did not prove that a class exists for every `S K`; the claim is only that the degenerate lists cannot work uniformly.

## No native theorem avoids the port

- **`NumericalTotal` is proved only on the legacy side.** In the module tree it occurs as the definition, inside `ValidWindow`, and as a hypothesis at `…FreshProbeDispatchProgramTargets.lean:25`. Its proofs are `exact_OriginalProbeTotal` and `exact_OriginalNumericalTotal`, both in legacy files.
- **The native tree has none of the needed machinery.** Searching `NativeModule/PersistentMarking` for `NumberedWindowAddressApplication`, `NumberedWindowFreeAddress`, `NumberedWindowTypedProbe`, `FreshArrowProbe` and `ClassApplicationGraph` finds only `…OriginalIntegrationTargets`, which uses `typed`, `probe` and `graph` in hypotheses.

## What forces the size

The dependency chain of the third conjunct, by declaration:

- `exact_OriginalProbeTotal` (file 15) calls `exact_FreshProbeApplication` (file 12).
- `exact_FreshProbeApplication` calls four suppliers:
  - `exact_TypedAddress` (file 12; its own suppliers are already native),
  - `exact_FreshArrowProbe` from `NumberedWindowFreeAddressChecks` (files 8–10),
  - `existsCode` (already native),
  - `exact_ClassApplicationGraph` from `NumberedWindowApplicationGraphChecks` (files 1–7).

So files 1–12 and 15 are forced by `NumericalTotal` alone. Files 13, 14, 16 and 17 add `formulaType`, the target statements, `TypeSupport` and `ChildClosed`. They are short, but 13 and 14 cannot be dropped, since files 15 and 16 import file 14 and it imports file 13.

## Equivalence check of the native dependencies

I compared native copies with their legacy originals at two levels and found no divergence.

**Statements used directly by the ported proofs** are textually identical, with line numbers shifted only by the four-line header:

- `exact_ScalarAddress`, `exact_ExactAddressView`, `admitted`, `exact_FiniteWindowBit`
- `rootInWindow`, `arrowRight`, `subtypeSelf`, `existsCode`
- `pairRound`, `roundtrip`, `currentPair`, `currentDecoder`

**Import structure** maps one-to-one, each legacy `import` becoming the corresponding `public import` under the native prefix, for:

- `NumberedWindowArithmeticAllContextAdmittedProof`, `…AllContextBits`, `…ClassAddressProof`, `…CoverBoundsProof`
- `…FieldAlgorithmChecks`, `…LeastClassChecks`, `NumberedWindowPathWitnessTargets`, `…PathWitnessClassCode`
- `NumberedWindowExternalApplication`, `…ExternalIDOperators`, `…ExternalTypeFactsTargets`

No current native theorem looks likely to break the port. The remaining risk is the twelve port bodies I have not read, not a mismatch in what they import.

## Staging for validation

The port can be checked in pieces, statements before proofs:

1. Statement files: 1, 5, 8, 11, 13, 14, 16.
2. Application graph proofs: 2, 3, 4, 6, 7.
3. Free address proofs: 9, 10.
4. Typed probe and probe totality: 12, 15.
5. Valid window: 17, then `exact_SelectInstalledWindows`.

Stage 1 already exposes any name-resolution problem in the native lineage, at the cost of statement-only files.
