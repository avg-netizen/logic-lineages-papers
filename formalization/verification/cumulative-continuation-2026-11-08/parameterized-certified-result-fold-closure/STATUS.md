# Checked: parameterized certified original result-fold closure

Three unchanged exact internal targets passed native Lean checking and actual
standard-axiom audits. Independent frozen-byte specification review and native
comparator-only preflight preceded proof authorship. Independent postproof
review remains pending.

The packet has 11 Lean files and 23 audited declarations, including three
exact aliases. All 1,217 current local imports have successful source-matched
rows across 84 immutable native receipts. All 1,227 frozen/input pins remain
unchanged, and all 1,218 broader frozen Lean inputs have successful native
matches. There are no new compiler warnings. This is cumulative focused
verification, not a fresh full-closure or full-root build.

## What is checked

- In every original positive body and context, certifiedFoldP is equivalent
  to the actual parameterized run with original singleton visit work, empty
  initial results and singleton output, at literal succ(payload+payload).
  Actual encoded initial and terminal state witnesses remain present.
- Actual openGuardP(value,p)=0 and L(value,p)=out internally imply certified
  fold success and the actual output. Payload/work/result/state witnesses
  are produced internally. Zero output is allowed.
- Original application constructor graphs, G(parent,p)=1, certified children
  at the same p and C(d,e,functionOutput,argumentOutput,p)=out internally
  imply parent certification at its own original fuel.

Certification always conjoins actual goodRunP=1 with actual foldP=out. The
unchanged goodState checks exact-one status, empty work and exactly one
result. A singleton zero is accepted; the raw output selector's default zero
is never used as evidence that a malformed or unfinished state succeeded.

## Reuse and boundaries

The proofs reuse the original state-shape bridge, initial-state and payload-
fuel facts, unchanged constructor queries and original application fuel
arithmetic. Parameterized local transition equations, work composition and
result-suffix framing preserve the complete original result stacks and the
same symbolic parameter. Empty-work terminal padding consumes only the
remaining original parent budget. It does not introduce new fuel or assert
that a padded first run leaves an appended work suffix untouched.

No external calibration, evaluation-extensionality or semantic truth-to-
derivability reflection supplies these internal proofs. The parameter is
never encoded in the original state, work frame or result entry. All three
targets retain arbitrary body, context and symbolic terms.

This does not prove unconditional internal goodRun acceptance, canonical leaf
selection, representative identification/congruence, uniform canonical/path
correctness, unconditional CertifiedApplicationLift, source constructor/
lambda/substitution closure, all-term accessibility or paper06 lem:id1.
No numbered source target is promoted.

## Gates and release

- Preflight: `build-reports/1794155483927722596-6.json`.
- Final exact gate: `build-reports/1794155803273920432-6.json`.
- Actual axiom closures use only propext, Classical.choice and Quot.sound.
- Peak successful closure process-tree RSS: 1,176,760 KiB.
- Peak successful component process-tree RSS: 1,094,948 KiB.
- Unchanged profile: 2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum free,
  one thread, 90 CPU seconds, 180 wall seconds and pinned upstream cache.
- All seven checker sessions ended; sole compiler admission was released at
  2026-11-08 16:37:10 UTC with both shared locks verified free.

Three proof-only namespace/identifier failures and their exact source
candidates are preserved locally. No frozen statement or supplier changed;
no failed output or sorryAx dependency is accepted. The initial frozen
specification and correspondence remain byte-identical historical records;
this status and ACCEPTANCE.json supersede their pending-proof descriptions.
No Git, global-register, dependency, resource-policy, CI or publication action
was taken.
