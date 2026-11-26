# P16 original boundary reports on the shared physical tapes

Source-only gate: `NumberedWindowInternalDirectBoundaryAtSharedTapesProof.exact_OpenBoundaryAtSharedTapes`.
Lean source SHA-256: `ec83c6ec5a642d9da2ed8b2edf6cf4f03163dca94f44e2cb46e655131c221dc0`.

The original directLists scalar typing and nonempty-removed boundary
are applied to the original raw input order [source,target,removed].
The input's three known positive parser reports are on exactly those
same raws (normally provided by #1515's shared report). The original
#1510 exact_OpenRawGuards parses and evaluates the one actual boundaryRaw
call. For each of its outputs, parser graph value uniqueness at its
own unchanged raw input, followed by object successor cancellation,
identifies the physical scratch payload. Input transport of the two
actual typedScratch graphs and output transport of actual consCode
put the three reports on the known shared scratch terms. The same
bound head/tail and object context are retained. Arbitrary object
goal and context relabeling are preserved. No independent parse
choice, numeric reflection, or overall original direct theorem.

Supplier pins: DirectBoundaryOpenProof `21905aa9513a01ff13ecc7a21c6d703026e16d0cc9ad15fc5ad112935955dcd0`;
DirectSourcePartitionRawGraphProof `42ef4c0c527ce2ca12d02a31450242bb1db87e9044627a764ed25c92605cab0e`.
