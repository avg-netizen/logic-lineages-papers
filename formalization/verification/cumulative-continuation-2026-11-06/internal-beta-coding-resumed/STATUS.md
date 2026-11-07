# Accepted internal bounded collection and beta coding

The original internal calculus now proves **full bounded beta coding for arbitrary relations and object-language bounds**. This is a supporting arithmetic-coding component for paper06 `lem:id1`. The numbered register remains **168 checked, 2 inherited, 19 pending / 189**; no numbered statement changes status.

## Exact mathematical scope

For every original positive body, arbitrary free-variable type, arbitrary expanded-language relation `R(i,r)`, and arbitrary original arithmetic term `n`, the calculus derives bounded collection:

\[
(\forall i<n\,\exists r\,R(i,r))
\;\longrightarrow\;
\exists K\,\forall i<n\,\exists r\,(R(i,r)\land r<K).
\]

It also derives the full shared-code theorem:

\[
(\forall i<n\,\exists r\,R(i,r))
\;\longrightarrow\;
\exists a\,\exists b\,\forall i<n\,\exists r\,
(R(i,r)\land\beta(a,b,i,r)).
\]

Both code components precede every index and dependent residue witness. The beta formula is the unchanged `OrdinaryArithmetic.betaFormula`, embedded into the existing original calculus. All free parameters and correlations remain shared. The theorem includes zero bounds and does not assume functionality, an external finite sequence, a supplied witness bound, supplied moduli, supplied coprimality, or a coding oracle.

The exact main alias is:

```lean
LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingStatementChecks.actualBoundedBetaCodingExact
  : LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingTargets.ActualBoundedBetaCoding
```

## Construction

The collection proof uses actual object-level PA induction. The empty range uses bound zero; the successor case combines the previous bound `K` and last witness `r` into `succ (K + r)`.

The coding assembly obtains a suitable positive difference common multiple internally and enlarges it to `B = (b + 1) * (K + 1)`. The exact residue suppliers prove that this scaling preserves every required divisor and places every retained witness below each literal beta modulus `1 + (i + 1) * B`. The accepted modulus theorem supplies pairwise coprimality.

Relational CRT is applied to the original relation conjoined with its strict witness bound. Each selected residue therefore keeps both its original relation and its bound. Bounded congruence then yields the literal original beta formula. Genuine existential rules introduce the shared code pair and eliminate the temporary bound and multiplier.

## Native verification

| Item | Result |
| --- | --- |
| Focused coordinator | `LogicLineages.ExternalCheckpoint20261106InternalBetaCoding` passed |
| Current local source matches | **852 / 852** |
| Exact frozen-target aliases | **4 across 3 gates** |
| Main and collection aliases | `actualBoundedBetaCodingExact`, `actualBoundedCollectionExact` |
| Residue supplier aliases | `scaleMultiplesExact`, `residueBoundExact` |
| Permitted axiom set | `propext`, `Classical.choice`, `Quot.sound` |
| Peak successful process-tree RSS | **1,220,048 KiB** |
| RSS / heap / minimum-free limits | **1,536 / 2,048 / 2,048 MiB** |
| Workers / CPU / wall limit | **1 / 90 seconds / 180 seconds** |
| Successful final receipt | `native/1794019992869901960-5.json` |

The residue-bound alias uses only `propext` and `Quot.sound`; the other three aliases use the standard three. The focused coordinator and every exact gate passed in one completed final invocation. All five frozen definition/target files remain byte-identical to the paused originals and passed fresh preflight before resumed proof edits.

The toolchain remains Lean `4.32.0-rc1` with Mathlib commit `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`. Twenty-one missing official compiled cache entries were restored. No upstream source build, checker edit, dependency change, or resource-limit increase was used.

All seven resumed native receipts and their logs are retained. The initial missing-cache failure and four proof-elaboration failures are recorded separately. Exact failed source versions are preserved under `attempts/`; the original paused failure and snapshots remain in the historical checkpoint. [PROOF-REPAIRS.json](PROOF-REPAIRS.json) records the repairs. [NATIVE-VERIFICATION.json](NATIVE-VERIFICATION.json), [SOURCE-PINS.json](SOURCE-PINS.json), and the independent reviews record source and axiom acceptance.

With the pinned runtime and populated cache, run from `formalization`:

```sh
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 \
  --threads 1 --cpu-seconds 90 --timeout 180 \
  LogicLineages.ExternalCheckpoint20261106InternalBetaCoding \
  LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionStatementChecks \
  LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalResidueBoundStatementChecks \
  LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingStatementChecks
```

## Preservation and remaining scope

Accepted integration `6153603a9e15686c7b6cbe3fc2b4e6c96ade8778` combines the word-guard checkpoint with all twenty subsequent internal arithmetic and CRT prerequisite commits. The paused commit `464b3e374c2f0f7c532e19cf935a412d6a112fe7` is preserved as historical provenance. This continuation resumes and completes its collection and beta-coding targets.

All 8,687 pre-existing Lean sources beneath `formalization/LogicLineages/` are unchanged from the accepted integration, and all 426 guard dependency pins match. The 12 paused source snapshots remain intact; three active draft proof files received elaboration repairs, and the beta assembly, endpoint, exact gate, and coordinator are four new source files. Shared metadata records the new supporting components and import without changing any numbered statement status.

General internal primitive-recursion representability, the remaining computability/constructor/lambda/fundamental derivations, and all-term accessibility remain pending. The whole endpoint `ContextUniformTargets.ActualContextUniformInternalAccessibility` and paper06 `lem:id1` are not completed by this supplier. This is a focused native result; no full-project or remote-CI build is claimed.
