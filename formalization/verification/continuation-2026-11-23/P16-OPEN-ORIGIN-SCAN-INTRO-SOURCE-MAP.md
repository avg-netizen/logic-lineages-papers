# Paper 16: reconstruct original side-local inserted scan

Paper 16, `sections/ordinals.tex`, lines 143–153. The union split must
reconstruct the original checker on both side sources. On an actual
scratch output cons, the first exact contract constructs the literal
`loopAccept` run from a checked same-head `rowAccept` and the same-pool
tail run. The second reconstructs the original `scan` from an
actual raw inserted tape parser success with that same scratch result
and its accepting loop, on the unchanged original raw removed input.

Exact gate `LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroProof`,
aliases `exact_OpenOriginScanConsIntro`, `exact_OpenOriginRawScanIntro`.
These laws construct object derivations. They are not the simultaneous
inductive split/traversal itself and do not derive the required parser
report or membership on a side.

Frozen Lean source hashes (SHA-256):

    db99e8b7f34836ed3e9e537e56b54c1e8f50a09c878d14ca6045a74189c0ae05  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOpenOriginScanIntroProof.lean
    6443f64f2e5b2d6be3b8cf20162e934c426fb9ca4fac1533faaea3a7a6f6b9ea  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOpenOriginScanIntroTargets.lean
