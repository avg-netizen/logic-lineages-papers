# Accepted supporting component: adjacent mixed-rank word guards

This isolated continuation starts from `229c6588` and preserves every tracked baseline source, manuscript, target, checker, dependency pin and register file. It adds supporting cases of paper08 `lem:guards`; no numbered source theorem is promoted. Register remains **167 checked, 2 inherited, 20 pending / 189**.

## Exact results

- Adjacent X ranks compare by expanding the higher source head once and immediately applying the checked shifted equal-rank guard. The unsigned higher occurrence remains attached to the original interior input.
- The X³/V boundary uses the exact exposed index `j-ceil(c/2)` and the checked shifted quadratic guard. Arbitrary signed depth indices, outer shifts and exact ties are retained.
- Arbitrary admitted A(x)/B(y) interiors remain original, and complete original/generated domains are proved. Actual source expansion and same-rank cutoff budgets are both paid.
- The local transformation preserves E count and every range-rank count except the opposite lower rank, where exactly one occurrence is removed. This includes the cubic/quadratic boundary and does not claim global termination.
- The retained-word constructor and both composed cutoff programs are uniformly primitive recursive.

## Verification

Gate: `LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.StatementChecks`.

All **230 local dependency modules** have successful native receipts matching current source hashes. All **4 exact frozen aliases** use only `propext`, `Classical.choice` and `Quot.sound`. Maximum successful observed process-tree RSS is **1,193,692 KiB**, below the unchanged **1,536 MiB** cap. Heap/free-memory allowances are 2,048 MiB, with one compiler worker and 90-second CPU/180-second wall limits. The sole native slot is released.

Definitions and targets were frozen and natively compiled before proof construction. Every new proof passed on its first native attempt; no target changes or repairs were needed. Existing exact-source local objects were reused. No upstream build/cache change, full-root build or remote-CI result is claimed.

## Remaining scope

Arbitrary mixed-rank gaps, terminal counter/leaf and nonlinear/leaf growth, complete guard recursion and ordinal termination, same-variable terminal decision, ranked row cancellation and current-occurrence nonlinear provenance remain pending. Closed existential word decision and full first-order BASE remain open. These are local adjacent-rank comparison branches, not the full guard theorem.

## Evidence

- `FREEZE.json`, `SOURCE-CORRESPONDENCE.md` and `SOURCE-PINS.json`
- `SEMANTIC-REVIEW.md`
- `NATIVE-VERIFICATION.json` and `BASELINE-PRESERVATION.json`
- `ACCEPTANCE.json` and `ACCEPTANCE-REVIEW.json`
- Complete native receipts and raw logs in `receipts/`

Only the new component and its evidence directory were added. The component is committed only on its isolated branch. No push or publisher-worktree edit is part of this delivery.
