# Cumulative continuation: original numeric root-checker effectivity

Branch: `formalization/cumulative-continuation-2026-11-03`.
Base: merged main `3c53370408aa36e44650a4846d6a398e19f91389`.

This checkpoint proves primitive recursiveness of the **complete original
`numericRootTest`**, including its original Direct, Select, Copy and Mul
certificate branches. It adds **19 fixed targets in six supporting components**.
All six exact gates and their focused aggregate passed the bounded compiler
and actual axiom audit. The inherited external and intervening local work are
already present through the merged base; they are not counted again as new work.

## New accepted results

| Component | Fixed targets | Result |
|---|---:|---|
| `NumberedMultisetPresentation` | 4 | Original typed packed-list and full multiset-certificate encoders and decoders are primitive recursive. |
| `NumberedFiniteMarkPrimrec` | 3 | Exact calibration and primitive recursion of the original finite marking, including initial lambdas, and of packed `markTarget`. |
| `NumberedMultisetTestsPrimrec` | 2 | Original indexed `replacementTest` and complete `multisetTest` are primitive recursive. |
| `NumberedCopyOperation` | 5 | Original head precedence, exact raw/typed Copy calibration, actual packed Copy and numeric Copy certificate checking. |
| `NumberedMulPrimrec` | 4 | Exact raw/typed Mul calibration and primitive recursion of the raw, original packed and original numeric Mul tests. |
| `NumberedNumericRootPrimrec` | 1 | The unchanged complete `numericRootTest` is primitive recursive on all its stated inputs. |

The whole-root theorem fixes finite signature size, arity and binder context
explicitly, and varies both finite window lists, the complete finite Boolean
precedence table and all source/target/certificate numbers jointly. Empty or
duplicate windows, arbitrary tables and malformed natural inputs are included.
The source-universe check, typed target reconstruction, selected occurrence,
positive Copy/Mul labels, type/head/window guards and selector payload rules are
unchanged. Abstraction, Beta and Bottom retain their zero-payload requirement;
unknown selector tags fail.

The Mul proof uses actual finite marking beneath lambdas. Root-only Put would
not establish this operation. Every kept, removed and inserted occurrence and
each literal removed-index/mark-label witness is retained. Missing or extra
witnesses and out-of-range indices fail as before; repeated indices and
permitted empty insertion remain available.

## Source register and inherited progress

The whole-source register remains **154 checked, 2 inherited and 33 pending out
of 189**. No numbered source statement is promoted by these supporting results.
Each of the six new components is linked to `lem:id1` and reused by
`lem:simulation` in `TARGETS.json`.

The intervening local checkpoint's source codec, primitive presentation, exact
`literalTypes`, and same-source-window structural translation were already
linked in the register. Its coverage summaries and remaining-dependency text
still described that fixed-parameter supplier as wholly pending. Those stale
descriptions are corrected here. Both endpoint representatives continue to use
one explicit `S = Ty(s)`. The remaining uniform-parameter and arithmetic
obligations are retained.

Inherited records remain separate:

- The preceding external ledger records 111 components / 374 fixed targets.
- The intervening local publication records 20 components / 106 declarations,
  across termination ordering, computability/knowledge and arithmetic comparison.
- This checkpoint records only its six new components / 19 fixed targets.

## Verification and preservation

The exact Definitions/Targets files were compiled and their hashes recorded
before candidate proofs. Every frozen specification remains unchanged. All
19 aggregate declarations have actual axiom closures contained in `propext`,
`Classical.choice` and `Quot.sound`. No new axiom or proof shortcut was introduced.

The focused aggregate is
`LogicLineages.CumulativeCheckpoint20261103RootEffectivity`. Its local import
closure contains **534 modules**, with source hashes and current compiled
objects verified. This checkpoint owns **28 new Lean files**, all in that
closure. The aggregate check took 1.273 seconds with peak observed process-tree
RSS 1,130,448 KiB, after its suppliers had been checked.

Checks used the unchanged serialized runner, one thread, 2048 MiB Lean heap,
1536 MiB RSS ceiling, 2048 MiB free-memory floor, and per-module 90-second CPU /
180-second wall limits. Existing pinned upstream objects were reused. The
root import inventory includes every new gate and the aggregate; a new full-root
build or GitHub CI run is not claimed.

The original manuscript and all original operation/certificate definitions
remain byte-identical to the base. Prior accepted ledgers, existing source
statuses, declarations, comparators and recorded source issues are preserved.

## Remaining mathematical work

The next computational obligation is the original contextual checker. Its
`focus` operation can extend `holeGamma` under lambdas. `stepTest` then calls
the unguarded `selectorTest` at that discovered context. A theorem for each
fixed context does not alone establish that joint computation, and replacing
the selector by guarded `numericRootTest` requires an additional confinement
argument.

Still open are exact effective focus/replacement, the genuinely context-uniform
selector/decoder interface, numeric step/quotient-edge/positive-path checking,
arithmetic formulas for the unchanged H and positive closure R, source-required
varying-parameter interfaces, whole-source simulation assembly, internal ID1
accessibility and ordinal suppliers. The recorded ordinary-source transitivity
obstruction and the paper08 kernel-convention issue remain unchanged.

## Evidence

- [Frozen specifications](termination-ordering/ROOT-EFFECTIVITY-FREEZE.json)
- [Accepted targets, exact hashes, audits and compiler receipts](termination-ordering/ROOT-EFFECTIVITY-ACCEPTED.json)
- [Focused local source closure](termination-ordering/SOURCE-CLOSURE.json)
- [Source-register dependency reconciliation](termination-ordering/SOURCE-REGISTER-PROGRESS.json)
- [Precise next contextual-checker dependency map](termination-ordering/NEXT-CONTEXTUAL-CHECKER.md)
