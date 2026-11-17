# Independent preflight review — raw lambda dynamics

Decision: **accept the frozen supporting scope**. Reviewed against branch base
`73709637b4997891d26ad5651628a44a8ac38392` on 2026-11-17.

## Frozen statements

- `Targets.lean`: `b816a3cab57a4bbfe47d167080cdbea8c6397af741b4a7ab2fbf52f67944826c`.
- `ComparatorGate.lean`: `5defb8dbdccea524def770215fdbf7a57dbd17c242f75f852fb113b6debbffd2`.

Both hashes independently match `FROZEN-COMPARISON.json`. The comparator expands
the two targets to the existing typed `RawStep`, `RawSteps`, and descending
`Acc` propositions with unchanged quantifiers.

## Source correspondence and proof viability

Paper 6, the proof of `lem:id1`, uses induction on accessibility of a lambda
body. The existing raw auxiliary rules allow a lambda source to reduce only
through a body reduction or to same-type bottom. Bottom has no reduct. Thus
finite paths from a lambda either end at bottom or remain lambdas along a
finite body path; the direct bottom rule supplies the reverse bottom case.
Accessibility is preserved by induction on body accessibility and reflected
by lifting every body step through the original lambda constructor.

All original raw reduction constructors remain present. No head-order,
subtype-closure, normalization, finite-window, or accessibility premise is
added. The orientation in `Acc (fun successor source => RawStep source
successor)` is the intended descending orientation.

The existing `NumberedRewriteApplicationPathProof` covers path composition and
function-side application transport. No existing raw lambda path
factorization or lambda/body accessibility equivalence was found in the
examined numbered-reduction sources. Internal certificate/lambda modules
operate at a different interface and do not supply these native statements.

Semantic source pins:

- `06-godel-t-termination-ordering/paper.tex`:
  `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`.
- `NumberedRewriteReductionDefinitions.lean`:
  `9bc140fb4cc06f91daf400e083f76d7f5f3036746b5e3e819806c39f2458ee2f`.
- `NumberedRewriteApplicationDefinitions.lean`:
  `471feb178305cd5182ae903e855ecf4222f22a5af9e6af7cb3d0acb6d15bb984`.

## Verification and limits

Independently inspected root's native preflight receipt
`build-reports/1794954950976448898-2.json`: 16 local modules, no failed row,
one worker, 2048 MiB heap, 1536 MiB process-tree RSS, 90 CPU seconds and
180 wall seconds per module, with a 2048 MiB free-memory floor. This review
launched no compiler and does not yet accept candidate proof artifacts.

These are native raw-reduction supporting results. They do not construct an
internal ID1 derivation, quotient-path transformer, final canonical-fold
coherence, substitution/fundamental lemma, full paper-6 accessibility,
stable-pair repair, or ordinal-height theorem. No numbered promotion follows.
