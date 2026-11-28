**Manifest for the 17-file port.** I have now read all 17 legacy bodies. Nothing is compiled.

Notation: `L/` is `LogicLineages/PersistentMarking/`, `N/` is `LogicLineages/NativeModule/PersistentMarking/`. In import lines, `N.` is `LogicLineages.NativeModule.PersistentMarking.` and `P.` is `LogicLineages.PersistentMarking.`.

## Rewrite rule

Every file takes this header, with the legacy namespace line and body kept verbatim:

```lean
module

public import <rewritten imports>

@[expose] public section

namespace LogicLineages.PersistentMarking.<unchanged>
```

Each legacy `import P.X` becomes `public import N.X`, except for six shared module files that have no native copy and must keep `P.`:

- `NumberedWindowAddressApplication` (file 1)
- `NumberedWindowFreeAddress` (file 8)
- `NumberedWindowTypedProbe` (file 11)
- `NumberedWindowComputabilityReading` (file 13)
- `NumberedWindowProbeCode` (file 14)
- `NumberedWindowInternalFreshProbeDispatchWindowTargets` (file 16)

All six are `module` files with `@[expose] public section`.

## Files in dependency order

Source is `L/<name>.lean`, destination is `N/<name>.lean`, with `NumberedWindow` abbreviated to `NW` in file names below.

| # | Name | Rewritten imports |
|---|---|---|
| 1 | `NWAddressApplicationTargets` | P.`NWAddressApplication`; N.`NWArithmeticScalarTargets`; N.`NWExternalApplication`; N.`NWPathWitnessTargets` |
| 2 | `NWAddressApplicationClassProof` | N.#1; N.`NWArithmeticAllContextAdmittedProof`; N.`NWArithmeticLeastClassChecks` |
| 3 | `NWAddressApplicationDecodeProof` | N.#1; N.`NWArithmeticScalarChecks`; N.`NWArithmeticAddressAlgorithmChecks`; N.`NWArithmeticFieldAlgorithmChecks`; N.`NWArithmeticClassAddressProof` |
| 4 | `NWAddressApplicationChecks` | N.#3; N.#2 |
| 5 | `NWApplicationGraphTargets` | N.#1 |
| 6 | `NWApplicationGraphProof` | N.#5; N.#4; N.`NWArithmeticAllContextAdmittedProof` |
| 7 | `NWApplicationGraphChecks` | N.#6 |
| 8 | `NWFreeAddressTargets` | P.`NWFreeAddress`; N.`NWExternalTypeFactsTargets`; N.`NWArithmeticAllContextBits`; N.`NWPrimaryCoverSyntax` |
| 9 | `NWFreeAddressProof` | N.#8; N.`NWArithmeticFieldAlgorithmChecks`; N.`NWArithmeticAllContextAdmittedProof`; N.`NWPathWitnessClassCode`; N.`NWExternalTypeFactsChecks`; N.`NWArithmeticCoverBoundsProof` |
| 10 | `NWFreeAddressChecks` | N.#9 |
| 11 | `NWTypedProbeTargets` | P.`NWTypedProbe`; N.#8; N.#5 |
| 12 | `NWTypedProbeChecks` | N.#11; N.#10; N.#7; N.`NWArithmeticScalarChecks`; N.`NWArithmeticAddressAlgorithmChecks`; N.`NWArithmeticAllContextAdmittedProof`; N.`NWPathWitnessClassCode` |
| 13 | `NWOriginalComputabilityFormulaTargets` | P.`NWComputabilityReading`; N.#5; N.`NWExternalComputability` |
| 14 | `NWOriginalProbeTotalTargets` | P.`NWProbeCode`; N.#13; N.#11 |
| 15 | `NWOriginalProbeTotalChecks` | N.#14; N.#12; N.`NWActualPairAlgorithmChecks` |
| 16 | `NWInternalFreshProbeDispatchOriginalWindowTargets` | P.`NWInternalFreshProbeDispatchWindowTargets`; N.#14 |
| 17 | `NWInternalFreshProbeDispatchOriginalWindowChecks` | N.#16; N.#15; N.`NWArithmeticScalarChecks`; N.`NWArithmeticAddressAlgorithmChecks`; N.`NWTypingBitsChecks`; N.`NWApplicationDomainProof` |

Every `N.` dependency that is not one of the 17 exists as a file under `N/`.

## Body references checked against the native tree

Every declaration the bodies name outside the 17 files exists natively under the same name:

- **File 2:** `exact_LeastCodeSpecification`, `exact_LeastCodeReflectsActualQuotient`, `canonical`, `round`, `NumberedWindowArithmeticPathDecodeProof.termAt`, `appCarrier`, `appClass`.
- **File 3:** `exact_ScalarAddress`, `exact_LeastRepresentative`, `exact_ExactAddressView`, `exact_ExactTaggedNodeCodec`, `exact_TyCodec`, `exact_TermCodec`, `pairRound`, `currentPair`, `currentDecoder`.
- **File 6:** `read`, `round`, `canonical`.
- **File 9:** `exact_VariableComputability`, `sameClass`, `NumberedWindowArithmeticCoverBoundsProof.term`, `exact_FiniteWindowBit`, `rootInWindow`, `arrowLeft`, `subtypeSelf`, `termBounds`.
- **File 12:** `admitted`, `existsCode`, `roundtrip`, `currentDecoder`, `pairRound`.
- **File 13:** `Least`, `taggedStep`, `ComputableClass`.
- **File 17:** `exact_ScalarAddress`, `exact_ExactAddressView`, `exact_FiniteWindowBit`, `rootInWindow`, `arrowRight`, `subtypeSelf`.

No body references a legacy-only declaration. The only way a legacy declaration could enter is a wrong import path, so the six `P.` exceptions are the lines to review.

## Places where the uniform rewrite may not be enough

These are namespaces a body opens or qualifies without importing the defining file directly. The legacy files relied on transitive imports. The native tree mirrors the import structure where I compared it, but I did not trace these particular chains to the end.

- **File 3** opens `NumberedWindowArithmeticAtomCodeChecks` (for `exact_TyCodec`). `NumberedWindowArithmeticTermCodeChecks` is reachable through `ScalarTargets` and `ArithmeticLeastClass`; I did not find the chain to `AtomCodeChecks`. If it fails with an unknown namespace, add `public import N.NumberedWindowArithmeticAtomCodeChecks`.
- **File 9** opens `NumberedWindowTypingBitsChecks` (for `exact_FiniteWindowBit`). Its only native importers are `NumberedWindowPrimaryExchangeBits` and `NumberedWindowRawWitnessChecks`. If it fails, add `public import N.NumberedWindowTypingBitsChecks`.
- **File 9** also uses `Primary.rec (motive_2 := fun _ _ _ _ _ => True)` and `simp [heads]`. These depend on the native `NumberedWindowPrimary` and `NumberedWindowDomain` having the same inductive shape as the legacy ones; both files exist natively, but I did not compare their contents.
- **Files 3 and 9** use `NumberedWindowFieldAlgorithm.pack` and `packNode`. That file has no native copy, so it is a shared module reached through the native field-algorithm files.

Six files contain `private` declarations inside what becomes an exposed public section: 2, 3, 9, 12, 15 and 17. Each is used only inside proofs in its own file.

## First compilable prefixes

- **Smallest:** file 1 alone. Top target `LogicLineages.NativeModule.PersistentMarking.NumberedWindowAddressApplicationTargets`. It contains only definitions, and already tests the mix of the native `fixed`, native `appClass` and `ActualCodeAt`, and the shared `application`.
- **Smallest with proofs:** files 1–4. Top target `LogicLineages.NativeModule.PersistentMarking.NumberedWindowAddressApplicationChecks`, which prints axioms for `exact_DecodedApplication` and `exact_ClassApplication`. File 3 is the first place the `AtomCodeChecks` question is answered.

After that, in order: file 7 (application graph), file 10 (free address, answering the `TypingBitsChecks` question), file 12, file 15, file 17.

## Constraint

No ported file may be imported together with its legacy original, since each pair declares the same names. The legacy files and their current importers stay as they are.
