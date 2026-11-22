# Paper 16: actual fixed window-to-grammar type inclusion

The fixed settings are the original `NumberedWindowArithmeticScalarTargets.fixed S K`. Their window type list is the original `(K.filter (fun σ => typesIn K (subtypes σ))).map encodeTy`, while the grammar type list is the original `K.map encodeTy`. Thus every code found in the first list occurs in the second, including when the proposition is quantified over raw inputs rather than scoped to predecoded types.

The guard conclusion uses the existing `TypeGuardCalibrated (fixed S K) T` premise. It relates a numerical output of 1 of that exact calibrated guard to membership in the unfiltered grammar type list. This discharges the numerical inclusion at the fixed-source boundary, not open derivability from the graph of an arbitrary extensionally calibrated program. It neither moves term occurrences across depth or maximum-numeral bounds nor establishes unconditional own-cover membership, address matching, or any numbered result.

Source correspondence: `NumberedWindowAdmissionTargets.window`, `NumberedWindowArithmeticScalarTargets.fixed`, and `NumberedWindowInternalAuxWindowMemoTargets.typeGuard`. The unresolved open boundary is described in the owner's [paused Paper 16 handoff](../local-three-agent-continuation-2026-11-21/P16-LOCAL-PROOF-LANE-PAUSED-HANDOFF.md).
