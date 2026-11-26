# Native ranked-constructor induction suppliers

Source: `06-godel-t-termination-ordering/paper.tex`, lines 605–619 in the
current manuscript, the constructor paragraph of `lem:id1`. The induction
parameters are head class, base multiset, finite label (then omega), and extra
multiset. The finite ranked signature has strict total precedence above the
native constant class, above the application class (lines 79–83).

This packet supplies exactly three native facts and no constructor-computability
endpoint. It retains the existing source semantics and the literal global
`rankCertificateTest table rank = true`, not an arbitrary chosen height.
Accepted `RankedPrecedenceCertificateProof.actualHeadRankCalibration` and
`RankedPrecedenceChainsProof.actualHeadClassRank` calibrate that rank to the
original head relations. The later context-uniform endpoint already requires
strict total precedence; decoding and using its actual certificate is later work.

1. `ActualPrimitiveMultisetQuotientDescent` maps the original
   `NumberedRewriteReduction.PrimitiveMultiset` witness to
   `DirectMultisetPresentation.Direct` for positive paths of the SAME
   `NumberedQuotientPaths.QuotientEdge`. Its source list is in the actual finite
   universe. The kept/removed/inserted occurrence witness is mapped literally,
   removed stays nonempty even when codes collide, and each inserted occurrence
   is dominated by an actual removed occurrence. The original finite mark gives
   one actual quotient edge using the accepted
   `NumberedWindowOccurrenceProof.finiteMarkStep`; that theorem is not refrozen.
   No target-universe or accessibility premise is introduced.
2. `ActualPrimaryOrdinaryMeasures` preserves ordinary root shape and the exact
   certified head rank, with a permutation of the typed least-code base list.
3. `ActualPrimaryNumberedMeasures` works for every finite label `k` and preserves
   that label and actual head rank. Its base-code permutation and ordered
   extra-code equality are distinct conclusions. The already accepted combined
   numbered-member permutation alone would not suffice for the lexicographic
   induction, so this statement does not weaken to that combined observation.

The list observation is exactly `SourceZeroNumberedComputability.argumentCodes`,
which keeps each original member type paired with its least representative code.
The accepted `SourceZeroNumberedShapeProof.primaryTypedCode` and
`argumentCodesPrimary` supply the typed child equalities. No new relation,
observer soundness, constructor C, Acc, whole well-foundedness or successor
closure is assumed. The full ordinary/numbered constructor induction remains
pending and is to be specified separately after these suppliers are reviewed.

Frozen packet: `SourceRankedConstructorSuppliersDefinitions.lean`,
`SourceRankedConstructorSuppliersTargets.lean`, and
`SourceRankedConstructorSuppliersPreflight.lean` in
`LogicLineages/OrdinalComparison/TerminationOrdering/`. Coordinator freeze and
serialized preflight are required before proof authoring. This author has run
no compiler and no Git action.
