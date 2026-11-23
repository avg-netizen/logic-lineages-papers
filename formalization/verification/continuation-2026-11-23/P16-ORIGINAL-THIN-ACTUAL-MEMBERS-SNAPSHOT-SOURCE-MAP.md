# Paper 16 supporting actual terminal members-snapshot (source freeze)

Gate: `LogicLineages.PersistentMarking.NumberedWindowInternalThinActualMembersSnapshotProof`
SHA-256 `84f62ecce52a24cb33a22be207e5fcf6beeb3dc3d98ee6e1492819616f94aa1a`.

* `snapshot` is the object formula
  `unary poolLength size vertices ⊓ (roundGraph E pool size vertices ctx ty seed ⊓ prefixed E vertices ctx ty pool later)`.
  The exact ordered vertices and pool are retained; this is not a set assertion.
  `snapshotRename` is variable relabeling only.
* `exact_OpenThinActualMembersSnapshot` selects the original physical length via
  `programCases poolLength`, then applies `exact_OpenMembersAtLength` to the genuine
  held `members E` output at the same vertices/context/type/seed, using the
  real length graph. It selects the actual next pass through
  `exact_OpenThinMembersPrefixedCases` and transports both already obtained
  reports into the one actual context of the prefixed report. The continuation
  receives both real witnesses and the three conjuncts together.
* Inputs retain the actual original count bound, exact retained predecessor
  and actual single-step strict uncovered decrease used by pre-fixed closure.
  No length, round, successor-pass or pre-fixed report is supplied by the caller.
  This leaf does not prove cross-seed inclusion, paired matching, representative
  or least equality, or an unrestricted printed statement.

Exact supplier source pins:

* `NumberedWindowInternalThinActualMembersPrefixedProof.lean`:
  `a30497514ee2ff1ee16cfd36ae6feced40568ab9dc613b4d9b5c8ce207ffa6d3`.
* `NumberedWindowInternalSparseOpenRoundsChecks.lean`:
  `974dbe9772b6b1f0aa69015718072f892a46733a51bef252df001fbc75112808`.

This document records the initial source freeze, not native acceptance.
