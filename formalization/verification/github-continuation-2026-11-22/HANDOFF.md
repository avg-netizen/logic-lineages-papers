# Measured installation and supplied-policy bridge — 22 November 2026

Base: `dd4eddff9f8eab0a4532e8df4880f71b8d5dffb9` on
`formalization/new-paper-set-2026-11-18`. Local continuation branch:
`formalization/github-measured-install-2026-11-22`.

**Checked local checkpoint: 11 new Lean modules, five supporting records
(#1430–1434), and 13 exact theorem aliases. Both bounded native gates passed.
The owner authorized commit and push to
`formalization/github-measured-install-2026-11-22`.**

The prior handoff is already present in the base commit; its statement that
the preceding round was uncommitted described an earlier local state.

## Accepted supporting results

| Record | Exact aliases | Scope |
| --- | ---: | --- |
| #1430 | 4 | Concrete combined measured installation, carrier coordinates in both directions, application report, and edge measure preservation. |
| #1431 | 2 | Guarded application least existence and a common application least for functions with equal measured leasts. |
| #1432 | 1 | Application least existence from actual installed-scalar operand acceptances and their original same-context address reports. |
| #1433 | 3 | A joint partial-recursive supplied-code macro evaluator and its exact calibration to the existing policy macro. |
| #1434 | 3 | Both directions and the conjunction equating policy effectivity with selector-code realization. |

These are supporting interfaces and aliases, including conjunction aliases;
they are not 13 newly completed numbered source statements. The machine-readable
index is [root/ACCEPTANCE.json](root/ACCEPTANCE.json). Each record is appended under
`../new-paper-set-2026-11-18/accepted/` and pins its active source files, scope map,
and focused native evidence.

## Paper 16

The new `NumberedWindowInternalCoverCombinedMeasuredInstall` interface installs
one measured, paired, cover-guarded exchange throughout the edge, member and
packed-least programs. The same least program is used by the actual address
scalar and application frontend. The four exact installation statements cover
carrier-coordinate extraction and reconstruction, the original application
report, and selected-measure preservation.

The application-existence packet derives the application's least from the
original type guards and function/argument matching windows. Its class
continuation obtains one common application least from equal function leasts;
neither application least is an input. Function windows are retained explicitly
because a naked packed-least call does not establish a typed carrier.

The integration statement obtains both operand windows from actual accepted
installed-scalar addresses and their original reports at one shared context.
It derives application least existence with only the original syntax/refit
type guards left as explicit type premises. It does not yet establish an
accepted output address for the full application frontend.

Scope and target freezes: `measured-route/` and `application-existence/`.
Their append-only ledgers contain the final native outcomes. Any native-pending
wording in the frozen pre-proof source maps describes the freeze-time state;
the accepted evidence and subsequent ledger entries supersede that status.

## Paper 17

The source check in `p17/CORRESPONDENCE-REVIEW.md` finds no material mismatch
for the arithmetic circuit theorem or the standalone fixed-policy ground
theorem. The printed main theorem requires uniformity in a supplied policy
program, while its current comparator only supplies a decider separately for
each effective policy. Preserve the numbered main theorem as pending.

The checked macro interpreter takes a `Nat.Partrec.Code` as a genuine input and
uses the existing literal policy expansion. It is jointly partially recursive;
when the supplied code realizes the policy selector, it terminates and returns
exactly the existing macro result, including syntactic rejection. A separate
realization target equates the existing effective-policy predicate with the
existence of such a supplied code. These establish the first bounded interfaces
for the uniformity repair. Uniform source compilation and the full uniform
comparison procedure remain follow-up work.

## Remaining boundaries

- The original two type guards remain in paper 16.
- Arbitrary callback calibration to the manuscript and full installed-tuple
  source semantics are not established by the new executable bundle.
- An accepted application output address still needs the original output
  carrier/fixed-point reconstruction.
- Paper 17 still needs a code-indexed source compiler and uniform comparison
  procedure; joint dependence on a supplied near-control parameter should be
  exposed explicitly.
- No numbered promotion is made. Current register remains 156 checked and
  11 pending out of 167.

## Native validation

Root owned the single native queue. The unchanged wrapper ran
`scripts/check.py` at 2048 MiB heap, 1536 MiB RSS, 90 CPU seconds, 180 wall
seconds per module, one worker and a 2048 MiB free-memory floor.

| Gate receipt | Result |
| --- | --- |
| `1795389808644602588-12` | Passed the installation and application-existence proof modules with their 3,594-module dependency closure. |
| `1795394451020498412-12` | Passed the carrier integration, macro interpreter, and code-realization proof modules across the 3,712-module combined closure: 118 native compilations and 3,594 verified cache hits from the initial gate. |

All 13 named endpoints depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The observed peak process-tree RSS was **1418.4609375 MiB**, below
the unchanged 1536 MiB cap. Every requested proof module passed on its first
native attempt; the pre-proof keyword-name draft remains preserved in
`p17/drafts/`. Frozen target and definition hashes still match their ledgers.

The exact proof modules are:

```text
LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof
LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceProof
LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationProof
LogicLineages.PermittedControl.PolicySuppliedCodeMacroProof
LogicLineages.PermittedControl.PolicySuppliedCodeRealizationProof
```

The final gate invocation, from `formalization/` with the pinned compiler on
`PATH` and `LEAN_CHECK_LOCK_DIR` naming the existing `.lake/locks` directory, was:

```bash
bash verification/local-fable-pair-2026-11-22/gate.sh mathlib \
  LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationProof \
  LogicLineages.PermittedControl.PolicySuppliedCodeMacroProof \
  LogicLineages.PermittedControl.PolicySuppliedCodeRealizationProof
```

The final closure includes the two earlier new proof modules. Full named
receipts, focused theorem logs, and setup/gate transcripts are preserved in
[root/portable-native-evidence.zip](root/portable-native-evidence.zip); the ZIP's
SHA-256 is recorded in `root/ACCEPTANCE.json`. Per-record axiom output and source
pins are in `evidence/`. Verification used the native proof gate and focused
statement-to-source assessment; no separate manual proof-body acceptance is
claimed.

Pinned compiler and Mathlib setup are recorded in `root/SETUP.json`. The terminal
queue in `root/NATIVE-QUEUE.json` has no active or queued work. Both native
sessions have exited and been reaped, and no Lean/Lake/checker process remains.
The local run policy is paused; its terminal snapshot is
`root/FINAL-LOCAL-RUN-POLICY.json`.

`root/FINAL-CHECKS.json` records the unchanged baseline pins, matching new-source
and evidence hashes, empty native process queue, and publication status. All
previously tracked sources, manuscript files, dependency pins, compiler scripts,
CI, `AGENTS.md`/`README.md`, and target registers remain unchanged.

## Next mathematical steps

1. Continue Paper 16 from the actual installed carrier: construct the original
   output address and prove its scalar/fixed-point acceptance after application.
   Keep the two type guards explicit until their source calibration is supplied.
2. Lift Paper 17's existing finite source recursions to one evaluator accepting
   the selector code and prove calibration to `PolicySourceInterface.compile`.
   Preserve the distinction between possible divergence of an arbitrary code
   and syntactic rejection of a realized policy run.
3. Compose that compiler with the existing fixed-control decision interfaces,
   and separately expose joint computability in the supplied near-control
   parameter before strengthening the main comparator.

## Repository delivery

The local branch is `formalization/github-measured-install-2026-11-22`, based
on `dd4eddff9f8eab0a4532e8df4880f71b8d5dffb9`. The completed checkpoint consists
only of new Lean modules and new supporting evidence. The owner explicitly
authorized commit and push of this checked checkpoint with "Commit and push
please". Publication targets `formalization/github-measured-install-2026-11-22`
through a non-force push. This authorization satisfies the preceding handoff's
commit/push reservation. The checkpoint retains the recorded numbered register
and mathematical scope; no numbered promotion or main merge is included.
