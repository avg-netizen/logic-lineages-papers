# Checked: parameterized original result-stack local laws

Eight unchanged exact targets passed native Lean checking and actual standard-
axiom audits. Independent frozen-byte specification review and comparator-only
preflight preceded proof authorship. Postproof review remains pending.

The component has 12 Lean files and 53 audited namespace declarations,
including the eight exact aliases. The focused import closure contains
1,165 current-source-matched local modules across 51 immutable native receipts.
All 1,178 broader frozen Lean input files also have successful source matches.
All 1,186 frozen/original input pins are unchanged. There are no new compiler
warnings. This is cumulative source-matched focused evidence, not a fresh
full-closure or full-root build.

## What is checked

- All-input evaluation equals the ORIGINAL `transitionValue`, with G/L
  callbacks sliced at `[value,p]` and C at `[d,e,function,argument,p]`.
- Internal unary lifting and finite appended-parameter composition.
- Original opening, leaf, finish and empty-state graph equivalences, with
  arbitrary original bodies, contexts, symbolic terms and the same parameter.
- Every symbolic iteration count preserves the entire terminal original
  state under the existing parameterized iterator.

The original state encoding, work frames, source/list constructors, payload
fuel, initialization and output selection are unchanged. The parameter is
never inserted into work frames or results and contributes nothing to fuel.
The original arity-generic `returned` relation supplies internally quantified
callback results. The leaf and combine programs have no semantic correctness
or Boolean-range premises.

## Proof reuse and boundaries

The new proofs use original graph composition/recovery, state constructors,
branch rules and functionality. Opening reuses the accepted unary visit law
and original unary expansion after lifting only the small control envelope;
it does not copy the original 19-query construction. Terminal iteration uses
the accepted actual parameterized fixed-point interface.

The evaluation theorem is separate and is never used to reflect external
truth into an internal derivation. Parameterized work append, result framing,
full-run terminal shape, full fold correctness, representative identification,
uniform canonical/path correctness, unconditional `CertifiedApplicationLift`,
constructor/lambda/substitution closure and all-term accessibility remain
outside this packet. No numbered source statement is promoted.

The initial `FROZEN-SPECIFICATION.json`, `SOURCE-CORRESPONDENCE.md` and
`STATIC-CHECKS.json` remain byte-identical historical freeze records. Their
pending-proof/preflight descriptions are superseded by this status and
`ACCEPTANCE.json`, not edited retrospectively.

## Native gate and resources

- Preflight: `build-reports/1794153752162790670-6.json`.
- Final exact gate: `build-reports/1794154302557301972-17.json`.
- Eight exact alias axiom closures: only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Peak successful closure process-tree RSS: 1,176,760 KiB.
- Peak successful component process-tree RSS: 1,076,656 KiB.
- Unchanged profile: 2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum free,
  one thread, 90 CPU seconds, 180 wall seconds, pinned upstream cache.
- All ten checker sessions finished. Compiler admission was released at
  2026-11-08 16:12:30 UTC, with both shared locks verified free.

Failed attempts and their immutable receipts/logs remain local. Failed module
outputs are discarded; only current-source successful rows are accepted.
No Git action, register/dependency/resource-policy/CI change, full-root build,
remote CI or publication was performed.
