# Finite guards on original shifted inputs

This component connects the existing exhaustive finite equality masks to the
actual signed-shifted inputs of NormalForm Phi occurrences. Every occurrence,
including zero coefficients and repeated names, remains in the source list.
Comparisons compile the total natural truncation exactly, including below-domain
values; no original domain formula is moved or discarded.

The target for the active maximal-name branch uses the actual finite sign guard
and the previously frozen PlainPhiDominance threshold. It requires the literal
plain-Phi row test, a raw name maximal among original occurrences, and a surviving
block owned by that name. It does not assume an externally chosen leader or tail
sign. It does not cover inactive cancellation branches, hyperPhi, full finite
source-case assembly or global induction. Numeric-code primitive recursiveness
is not claimed by this seven-target semantic component.

## Active-only theorem boundary

The ActualFiniteActiveBranch target explicitly assumes PlainPhiDominance.active i r ν = true, together with the plain-row, threshold and maximal-name hypotheses. The finite activeSign formula is not a decision of the row sign when that activity hypothesis fails: cancellation can leave a nonzero linear remainder. No inactive branch or numeric-code primitive-recursive program is accepted here. All six source files and seven aliases were independently accepted; the whole source statement remains pending.
