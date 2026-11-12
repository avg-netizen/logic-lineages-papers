# Internal numeric sort: proposed next contracts

The original plan below is now partly implemented. The runtime sort/insert AST remains unchanged.

## Verified progress

- Original insertion-state coordinate: exact gate `1794487752651663252-17`.
- All-raw insertion commutation: exact gate `1794488100206908806-5`.
- All-raw sort-insertion absorption: exact gate `1794488494638256706-5`.
- Idempotence is authored against a separately frozen target and awaits its gate.

The adjacent-swap consumer is maintained separately. These results do not yet supply the arbitrary coded BASE-permutation bridge described below.

## Existing reusable source

`OriginalNumericListSortDefinitions` is the literal insertion-sort Program. Its insert state retains both the original suffix and the inserted suffix. `OriginalNumericListSortInternalProof` supplies original list-recursion nil/cons unfoldings; `OriginalNumericListSortValueProof` supplies base, before/after branch, insertion projection and sort-cons value helpers. Native insertion-sort/permutation calibration is separate and cannot discharge internal arithmetic graph obligations.

No internal coded permutation/count/histogram contract was found in the current ID1Completion library. Native typed argument permutation enumeration/counting is not such a contract.

## Minimal proposed sequence

1. Prove internally that the left projection of every actual insertState output is its original numeric list input. Expose insertion nil/cons graph equations with actual internal comparison tests; do not assume this coordinate as a supplier.
2. All-raw insertion commutation: four actual insertion graphs, inserting x then y and y then x into the same arbitrary numeric list, imply equal outputs. No sorted-input premise is needed. Strong induction uses actual numeric tail descent and internal order cases for x, y and the current head. Equality cases retain duplicate entries.
3. Derive local adjacent-swap sort invariance using one actual sorted-tail graph and the original sort-cons equations. The two permutations use literal original cons graphs. This is a reordering-generator law, not an arbitrary permutation completeness theorem.
4. Derive sort-insertion absorption: sorting an actual insertion agrees with inserting into the actual sorted input. The after branch uses induction and insertion commutation; the before branch follows sort-cons directly.
5. Derive all-raw sort idempotence from absorption and strong induction. No external sortedness or native list decoding is required.

## Remaining BASE boundary

These contracts preserve the multiset of numeric typed-observation entries locally. Lifting them to arbitrary original BASE exchanges still requires an internal witness/derivation connecting the actual source permutation condition to a finite sequence of these generators, or a separately proved internal multiplicity characterization. It is not justified by the native List.Perm theorem alone. They do not establish final canonical equality or class completeness.

Same-raw observation congruence for two child observer Programs is independent: it preserves the existing ordered argument spine and does not itself reorder BASE entries.

Update: all-raw idempotence exact alias passed, receipt `1794488585929683848-5`. Arbitrary coded permutation completeness and the original BASE exchange bridge remain separate obligations.
