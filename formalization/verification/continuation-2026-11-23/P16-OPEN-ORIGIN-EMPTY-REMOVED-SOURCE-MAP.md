# Paper 16: empty removed side has no inserted or projected row

The actual parsed empty removed side cannot accept an inserted row:
opening the original row validation produces genuine membership in the
empty scratch with exactly the same dominator. An actual nonzero
scratch input would expose an original head and an actual head
acceptance, contradicting that membership. Thus the accepted inserted
rows are exactly zero, and a successful actual projection of that same
list returns exactly zero. This enables the identical unchanged side
rather than repacking an equivalent replacement.

Exact gate: NumberedWindowInternalOriginEmptyRemovedProof. Audits at
exact_OpenScratchNonzeroCases, exact_OpenEmptyRemovedScanZero, and
exact_OpenEmptyRemovedProjectionZero. This does not equate arbitrary
permuted raw sources or complete the entire case split.

Frozen Lean source hashes (SHA-256):

    c88b1a85e11029407c25f795d9ead70db890bd251f758467010d878b8e83e6bf  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOriginEmptyRemovedProof.lean
    235e970e4e9aa395e9f8a03f88c737313a8119202c5fe857d8860c41d91c967c  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalOriginEmptyRemovedTargets.lean
