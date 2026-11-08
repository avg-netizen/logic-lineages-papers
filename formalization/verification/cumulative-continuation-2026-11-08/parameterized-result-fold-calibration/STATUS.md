# Checked: parameterized original result-fold calibration

Four unchanged exact targets passed native Lean checking and actual standard-
axiom audits. Independent frozen-byte specification review and comparator-only
preflight preceded proof authorship. Independent postproof review is pending.

The component contains five Lean files and twelve audited declarations:
eight proof declarations and four exact aliases. All 1,129 current local
imports have source-matched successful rows across 37 immutable native
receipts. All 1,138 frozen/input pins remain unchanged, and all 1,129 broader
frozen Lean inputs also have successful native source matches. There are no
new compiler warnings. This is cumulative focused evidence, not a fresh
full-closure or full-root build.

## What is checked

- The independent original payload-recursive semantic fold, sliced at the
  same arbitrary parameter, obeys its literal original opening/fallback
  equation on every raw input.
- The actual parameterized iterator returns the complete original encoded
  structured execution for every count, state and parameter, including
  count zero, non-one statuses, malformed frames and finish underflow.
- The actual run at exactly `2 * originalPayload + 1` returns status one,
  empty work and exactly one semantic result. The actual fold returns that
  same result for every raw original input and arbitrary parameter.
- The actual original whole-state check composed with that run evaluates to
  one. A singleton zero result is accepted; zero is never used as a failure
  criterion for the semantic output.

G/L remain arbitrary binary ASTs at `[value,p]`; C remains an arbitrary
five-argument AST at `[domain,codomain,functionOutput,argumentOutput,p]`.
No callback correctness, source validity, successful-run or positive-output
premise is added. The original state, work/results, source/list codes,
payload fuel, initial state and output selector remain unchanged.

## Reuse and scope

The proofs reuse checked parameterized transition and numeric-iteration
evaluation, the original encoded transition, independent semantic equation,
single-visit completion and singleton state selectors. The accepted original
completion theorem carries its existing meaning invariant, work-weight and
terminal-padding argument. These invariants and bounds are not redefined.
The independent semanticFoldP wrapper does not refer to runP, fuel or any
machine. The active parameterized composition packet is not a dependency.

All four results are external natural-number equalities. They do not supply
symbolic internal reflection, unconditional internal goodRun acceptance,
internal recursive constructor closure, canonical leaf selection,
representative identification/congruence, uniform path correctness,
unconditional CertifiedApplicationLift, lambda/substitution closure,
all-term accessibility or paper06 lem:id1. No numbered target is promoted.

The initial frozen specification, correspondence and static checks remain
byte-identical historical freeze records. Their pending-proof descriptions
are superseded by this status and ACCEPTANCE.json, not edited retrospectively.

## Native gates and resource release

- Preflight: `build-reports/1794155283105274038-8.json`.
- Final exact gate: `build-reports/1794155430604300098-5.json`.
- Every actual axiom closure uses only propext, Classical.choice and Quot.sound.
- Peak successful closure process-tree RSS: 1,176,760 KiB.
- Peak successful component process-tree RSS: 1,065,240 KiB.
- Unchanged profile: 2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum free,
  one thread, 90 CPU seconds, 180 wall seconds, pinned upstream cache.
- All three checker sessions finished. Sole compiler admission was released
  at 2026-11-08 16:30:43 UTC, with both shared locks verified free.

One proof-only argument-vector normalization failure is preserved locally
with its immutable receipt and candidate. The corrected proof passed all
audits without changing any frozen statement or supplier. No failed output
or sorryAx dependency is accepted. No Git, register, dependency, resource
policy, CI, publication or full-root build action was taken.
