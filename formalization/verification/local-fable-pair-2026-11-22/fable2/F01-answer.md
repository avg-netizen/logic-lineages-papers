Both statements passed the gate on the first attempt; nothing blocked, and the round theorem was not attempted.

| Statement | Theorem (proof module) | Receipt |
|---|---|---|
| `ExactOpenCoverCombinedRestrictedMeasuredPairedEdge` | `exact_OpenCoverCombinedRestrictedMeasuredPairedEdge` (`NW…MeasuredPairedProof`) | `build-reports/1795387172641849865-3159773.json` |
| `ExactOpenCoverCombinedRestrictedMeasuredPairedCommonLeast` | `exact_OpenCoverCombinedRestrictedMeasuredPairedCommonLeast` (`NW…MeasuredPairedCommonLeastProof`) | `build-reports/1795387310118722126-3160624.json` |

- **Hypotheses:** the two type-guard conjunctions, `windowAt W ctx dom arg`, and one function-level edge `edgeGraph Xm W ctx (rawCons dom cod) f g`. The reverse edge and the common function measure are recovered from that one edge, so neither is an input.
- **Conclusions:** `edgeGraph Xm W ctx cod a b` as a plain derivation; the second statement hands one common `x` with `leastGraph P.cover Xm W s ctx cod · x` at both applications to a continuation.
- **Axioms:** `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` for every public theorem; no `sorry`, `axiom` or `native_decide`.
- **Genericity:** no supplier was non-generic in the exchange. #1370 is only used at the unmeasured `directedX`, because the measure comparison is stripped off the function-level edge first; `guardedOfActualPair` was instantiated at the measured `Dm`.
- **Route deviation:** I called accepted `…PairedAux` rather than #1370 and the common-cover lemma separately, then upgraded its unmeasured edge with a new generic lemma `measuredUpgrade`.
- **Process deviations:**
  - The first targets hash went into the ledger after the proof file was drafted but before the first gate; the targets file was not changed in between.
  - I read `NW…RoundApplicationCombinedProof.lean`, `NumberedWindowInternalMeasuredAuxExchangeCompareProof.lean` and `NW…PairedCommonLeastProof.lean`, which the greps pointed to, and did not need `NW…DirectedXProof.lean`.
- **Duplicated helpers:** `edgeRename`, `Moved`/`move` and `shareLeast` are private upstream, so the new modules carry private copies; no existing `.lean` file was edited.
- **Records:** ledger section "F01 — measured paired step" appended; `fable2/MEASURED-PAIRED-EVIDENCE.json` and `fable2/MEASURED-PAIRED-SOURCE-MAP.md` written with the four file hashes.
