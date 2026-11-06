# Accepted supporting component: terminal nonlinear-word growth

This isolated continuation starts from `d7cc4ec3` and preserves every tracked baseline source, manuscript, target, checker, dependency pin and register file. It adds terminal supporting cases of paper08 `lem:guards`; no numbered source theorem is promoted. Register remains **167 checked, 2 inherited, 20 pending / 189**.

## Exact results

- Every admitted nonlinear letter dominates 2^t at the existing explicit letter tail. This includes the original independently scheduled E counter via `SourceProcessBridge` at c+d+1, not an unqualified companion substitution.
- Every admitted nonlinear word has all its actual successive domains and the source lower bound `2^(t-M) ≤ wordValue w t`, with computed M=`wordOffset w+1`.
- If the original raw inputs satisfy y≤x and both reach the explicit terminal cutoff, the shifted leaf y+b is defined and strictly smaller than the original nonlinear word at x. The same-variable case is included.
- The actual growth offset and both cutoff programs are primitive recursive. Arbitrary signed letter indices, repeated nonlinear occurrences and noncanonical unused fields remain supported.

## Verification

Gate: `LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.StatementChecks`.

All **171 local dependency modules** have successful native receipts matching current source hashes. All **5 exact frozen aliases** use only `propext`, `Classical.choice` and `Quot.sound`. Maximum successful observed process-tree RSS is **1,161,656 KiB**, below the unchanged **1,536 MiB** cap. Heap/free-memory allowances are 2,048 MiB, with one compiler worker and 90-second CPU/180-second wall limits. The sole native slot is released.

Definitions and targets were frozen and natively compiled before proof construction. One candidate attempt needed implicit-argument elaboration repair for `Nat.lt_two_pow_self`; the same repair was made in two not-yet-reached uses. No target, inequality, threshold or resource limit changed. All final proofs and aliases passed; one nonblocking tactic-style warning remains. Current failure counts are scoped to this component. Raw archives preserve older diagnostics separately, not as accepted current proof evidence. Existing exact-source local objects were reused. No upstream build/cache change, full-root build or remote-CI result is claimed.

## Remaining scope

All-shift leaf normalization, complete recursive guard construction and ordinal termination, general same-variable decision, ranked row cancellation and current-occurrence nonlinear provenance remain pending. Closed existential word decision and full first-order BASE remain open. Terminal growth is not the full guard theorem.

## Evidence

- `FREEZE.json`, `SOURCE-CORRESPONDENCE.md` and `SOURCE-PINS.json`
- `SEMANTIC-REVIEW.md`
- `NATIVE-VERIFICATION.json` and `BASELINE-PRESERVATION.json`
- `ACCEPTANCE.json` and `ACCEPTANCE-REVIEW.json`
- Complete native receipts and raw logs in `receipts/`

Only the new component and its evidence directory were added. The component is committed only on its isolated branch. No push or publisher-worktree edit is part of this delivery.
