# Accepted complete word-guard compiler

Paper 08 **`lem:guards` — Ordered maximum-variable guards — is checked**.
The source register is now **168 checked, 2 inherited, and 19 pending / 189**.
Only this numbered source statement changes status.

## Complete source coverage

For every original admitted finite-degree pair of words `A(x), B(y)`, with
arbitrary signed shifts and kernel indices, the actual total computable compiler
produces a common tail and three finite Boolean guards equivalent to strict,
equal, and reverse-strict comparison under `y <= x`. Its emitted row contains
only linear occurrences of the original maximum variable `x`; nonempty words
are applied only to the original `y`. No raw variable is replaced by an
independent fresh value.

The compiler also returns a fixed three-way answer for `A(x)` versus `B(x)`,
valid for every input on the same computed tail. The package includes the
complete finite trace of original and generated word pairs. All original,
generated, prepared, and output-row domains hold above the cutoff, independently
of the ordered-variable premise used by the comparison theorem.

The literal selected child decreases the existing counter-count/reverse-rank
histogram measure. Every local cutoff is accumulated before the tail is used.
The bounded syntax operations are primitive recursive; the full least-stopping
search and compiler are proved total computable. The invalid-input branch is
specified explicitly and stops immediately.

The whole-source alias is:

```lean
LogicLineages.OrdinalComparison.FullWordGuardCompletion.StatementChecks.fixed_fullWordGuards
  : LogicLineages.OrdinalComparison.FullWordGuardCompletion.Targets.FullWordGuards
```

## Native verification

| Check | Result |
| --- | --- |
| Focused coordinator | `LogicLineages.ExternalCheckpoint20261106FullWordGuards` passed |
| Current local source matches | **426 / 426** |
| New exact frozen-target aliases | **29** across three gates |
| Prior guard aliases preserved and checked | **77** |
| Total actual alias audits | **106**, all standard-only |
| Allowed axiom set | `propext`, `Classical.choice`, `Quot.sound` |
| Peak observed successful process-tree RSS | **1,188,808 KiB** |
| Unchanged RSS cap | **1,536 MiB** |
| Heap / minimum-free bounds | **2,048 / 2,048 MiB** |
| Worker / CPU / wall limits | **1 / 90 seconds / 180 seconds** |
| Successful coordinator receipt | `receipts/1793996097626807124-5.json` |

The pinned Lean version is `4.32.0-rc1`; Mathlib is pinned to
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`. Official upstream cache artifacts
were restored; no upstream source build, dependency change, checker change, or
resource-limit increase was used.

All sixteen raw native receipts and 438 module logs are retained. The nine
failed native candidates are preserved with exact source snapshots and indexed
in `PROOF-REPAIRS.json`. One auxiliary specification needed explicit parentheses
around an equivalence; both freezes and preflights are retained. The whole-source
target, all definitions, and every dispatcher/runner target remained unchanged.
The independent source and evidence reviews both approved acceptance.

To check the focused coordinator with the pinned runtime and populated cache:

```sh
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 \
  LogicLineages.ExternalCheckpoint20261106FullWordGuards
```

## Preservation and remaining work

The source freeze began at `2066300c`. Native evidence is anchored to
`e413aa1f`; the publication candidate preserves the further concurrent commit
`1c7c5f7b`. The four intervening commits add original finite-block, graph
composition, recursion-free totality/uniqueness, and universally closed graph
proofs. They do not overlap or alter the checked guard dependency closure.

Earlier finite-source comparison, uniform separation, scalar/vector hardness,
polynomial-collapse graphs, all fifteen local guard components, and the later
joint-Gamma work remain preserved. The only pre-existing files updated for this
checkpoint are the source register, current status headers, and the root import.

Ranked row cancellation (`lem:row`), closed existential word decision, arbitrary
first-order BASE, and the internal-level-two comparison consumer remain pending.
This is a focused native result; no full-project or remote-CI build is claimed.

`ACCEPTANCE.json`, `SOURCE-ACCEPTANCE-REVIEW.json`, `EVIDENCE-REVIEW.json`,
`NATIVE-VERIFICATION.json`, and `SOURCE-PINS.json` record the exact source,
declaration, hashes, checks, and register transition. Branch publication is
verified separately against the current remote head.
