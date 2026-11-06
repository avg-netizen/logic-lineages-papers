# Accepted supporting component: outer-shift normalization

This isolated continuation starts from `424d5021` and preserves every tracked baseline source, manuscript, target, checker, dependency pin and register file. It supports the initial and terminal cases of paper08 `lem:guards`; no numbered source theorem is promoted. Register remains **167 checked, 2 inherited, 20 pending / 189**.

## Exact results

- A primitive-recursive split returns the exact original prefix through the last non-shift and the maximal original shift suffix. Empty/all-shift words and unused shift fields are included.
- Summing only that signed suffix preserves values and domains whenever all original successive domains hold. The original `wordTail` is separately proved sufficient. No converse domain implication or cancellation across invalid intermediate truncations is claimed.
- Degree admission, E counts and every positive-rank range count are unchanged.
- Arbitrary all-shift/all-shift comparisons reduce exactly to integer-linear comparisons of their raw inputs and fixed signed sums.
- An all-shift left word against any admitted right word has an exact scalar linear view with all original domains paid. This is not a same-variable decision procedure or a syntactic formula compiler.
- An arbitrary nonlinear word at x dominates any original all-shift word at y≤x on the explicit combined cutoff, including x=y. All split, sum, normalized-word and cutoff maps are primitive recursive.

## Verification

Gate: `LogicLineages.OrdinalComparison.OuterShiftNormalization.StatementChecks`.

All **189 local dependency modules** have successful native receipts matching current source hashes. All **9 exact frozen aliases** use only permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Maximum successful observed process-tree RSS in the selected source-matched closure is **1,161,656 KiB**, below the unchanged **1,536 MiB** cap. Heap/free-memory allowances are 2,048 MiB, with one compiler worker and 90-second CPU/180-second wall limits. The sole native slot is released.

Definitions and the original eight targets were frozen and natively compiled before their candidate proofs. A complementary leaf/arbitrary-word target was added in its own frozen file and passed a separate preflight before its proof; the original frozen files remain unchanged. The final proof gate passed on its first attempt. There are **zero current-component failed native attempts**; raw archives retain eleven historical failures separately. One nonblocking unused-simp-argument warning remains. Existing exact-source local objects were reused. No upstream build/cache change, full-root build or remote-CI result is claimed.

## Remaining scope

Complete recursive guard construction and ordinal termination, general same-variable decision, ranked row cancellation and current-occurrence nonlinear provenance remain pending. Closed existential word decision and full first-order BASE remain open. These normalization/terminal cases are not the full guard theorem.

## Evidence

- `FREEZE.json`, `LEAF-WORD-FREEZE.json`, `SOURCE-CORRESPONDENCE.md`, `SOURCE-PINS.json`
- `SEMANTIC-REVIEW.md`
- `NATIVE-VERIFICATION.json` and `BASELINE-PRESERVATION.json`
- `ACCEPTANCE.json` and `ACCEPTANCE-REVIEW.json`
- Complete native receipts and raw logs in `receipts/`

Only the eight new Lean files and their evidence directory were added. The component is committed only on its isolated branch. No push or publisher-worktree edit is part of this delivery.
