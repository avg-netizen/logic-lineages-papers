# Closed-recognizer acceptance factor

All four frozen contracts are checked in eleven new Lean modules. The focused
gate has 1,439 source-matched native modules, all four exact aliases, and only
`propext`, `Classical.choice` and `Quot.sound` in the audited axiom closures.
All 631 frozen hashes match. Every inherited mathematical source is unchanged.
All compiler and evidence jobs for this checkpoint have finished.

The [native evidence report](runs/20261112T225138.976007Z/REPORT.json) records the
complete focused check. Its companion archives retain all native attempts,
including the repaired namespace-resolution failure, and their compiler logs.
The new namespaces contain 35 audited declarations.

## Mathematical scope

Let `C` be the unchanged explicit
`OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window`, and let
`L` be its unchanged underlying
`OriginalTransparentMixedDirectBottom.leaf H G M W oldStep`.
The new contracts use the same arbitrary source Program `S` throughout:

1. `FinishFactor` transfers `finish S C(out) = 1` to
   `finish S L(out) = 1` at the identical actual state.
2. `AcceptedStep` transfers an actual transition from `state` to `next`
   when `next` is nonzero, preserving the exact successor.
3. `AcceptingRun` transfers an accepting original-path run while preserving
   its path, initial state and final state, and proves destination finish
   acceptance at that same final state.
4. `RecognizesFactor` transfers recognition at identical source, target,
   certificate and runtime-parameter inputs.

The one-step proof preserves lambda-first priority. In the application case,
the old first-test rejection is retained. The accepted old leaf and any
proposed new first-guard acceptance would reconstruct old first-test
acceptance, giving a contradiction. Merely dropping the rejected first test
would not justify this result.

The run proof uses the original arithmetic strong-induction rule on the
original path. Both actual states are universally quantified inside each
induction row. The accepting suffix proves its initial state nonzero; the
successful-step theorem then reconstructs the same full run. The final proof
queries the path, live state and output once and recomposes the unchanged
recognizer. No native interpretation is reflected into an internal derivation.

The public exact contracts have no additional simulation, recognition or
induction supplier premise. Generic helper suppliers are discharged using
the concrete closed-checker factor and the independently proved local laws.

## Verification and preservation

Base: `4fea270b5f820b4a2b4bb02add9ccb8200bf8e56` on
`formalization/cumulative-continuation-2026-11-09`.

`FROZEN-TARGETS.json` records the independent contract review and target hash
before proof authorship. `FROZEN-SHA256SUMS` retains all 629 inherited recovery
entries and freezes the two new target/induction-definition files.

The native command uses the unchanged `scripts/check.py`, one compiler worker,
2,048 MiB heap, 1,536 MiB process-tree RSS, a 2,048 MiB free-memory floor,
90-second CPU and 180-second wall limits per module. The pinned Lean runtime
and official upstream artifacts are documented in `UPSTREAM-CACHE.json`.
This host uses an existing workspace directory for the checker's shared locks
because `/tmp` is absent; the checker and resource limits are unchanged.

From `formalization`, with the pinned Lean binary on `PATH` and
`LEAN_CHECK_LOCK_DIR` pointing to an existing shared absolute directory:

```sh
RECOGNIZER_NS=LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 \
  "$RECOGNIZER_NS.OriginalMixedClosedRecognitionStatementChecks"
python3 verification/continuation-2026-11-12-recognizer-factor/verify_evidence.py \
  --base 4fea270b5f820b4a2b4bb02add9ccb8200bf8e56 \
  --allow-inherited README.md \
  --gate "$RECOGNIZER_NS.OriginalMixedClosedRecognitionStatementChecks" \
  --alias "$RECOGNIZER_NS.OriginalMixedClosedRecognitionStatementChecks.finishFactor" \
  --alias "$RECOGNIZER_NS.OriginalMixedClosedRecognitionStatementChecks.acceptedStep" \
  --alias "$RECOGNIZER_NS.OriginalMixedClosedRecognitionStatementChecks.acceptingRun" \
  --alias "$RECOGNIZER_NS.OriginalMixedClosedRecognitionStatementChecks.recognizesFactor"
```

## Remaining scope

This factor does not assert recognizer equivalence or equality of transition
Programs on rejecting inputs. It does not identify the explicit checker with
an existing final tuple or extend the recognized trace language to arbitrary
source edges. General result-stack/root-return semantics, selected-endpoint
and final-tuple integration, unrestricted source-edge closure, internal I/C
and the original full accessibility theorem remain separate obligations.

The numbered register remains **171 checked, 2 inherited, 16 pending /189**.
This is a supporting component of paper06 `lem:id1`. No whole-paper promotion,
full-root build or remote-CI result is claimed.
