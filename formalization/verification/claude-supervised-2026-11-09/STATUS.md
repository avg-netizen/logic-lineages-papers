# Checked — original raw guard and selected-checker inversion

Two independently stated continuation contracts passed for the original
parameterized application checker. The proof internally recovers the original
constructor, path, endpoint and child-checker witnesses when its guard accepts.
When the guard is zero, it retains the original normalizer and unchanged
`oldChecker` leaf at the same inputs. Endpoint, checker, output, separate
parameter, formula body and context remain arbitrary.

| Exact contract | Result |
| --- | --- |
| `ActualAcceptedGuardElimination` | Eliminate an accepted original guard into internally recovered original constructor/child-transition facts, with full renaming and context-extension quantifiers. |
| `ActualSelectedCheckerElimination` | Split the actual selected checker into its original peeled branch or zero-guard branch, retaining the complete unchanged old-checker leaf. |

The proof contains eight audited supporting theorems. The 377-line returned
candidate compiled unchanged. Both independent exact aliases then elaborated;
all ten theorem dependency reports contain only `propext`, `Classical.choice`
and `Quot.sound`. No calibration oracle is used as an internal derivation rule.

This is a supporting component for paper06 `lem:id1`. The full
`ContextUniformTargets.ActualContextUniformInternalAccessibility` remains
pending, as do neutral quotient/shape inversion, unpeeled neutral-leaf closure,
arrow computability, lambda/substitution, multiset and constructor obligations.
The numbered register remains **171 checked, 2 inherited, 16 pending / 189**.

## Verification evidence

The unchanged bounded checker ran one thread with 2,048 MiB heap, 1,536 MiB
RSS, 2,048 MiB available-memory admission floor, 90 CPU and 180 wall seconds
per module. Candidate receipt `1794271668294249378-2994094` passed 1,189
module compilations; the candidate used 2.8 CPU seconds and 1,073,360 KiB RSS.
Exact-gate receipt `1794275789317692569-3010028` passed with 1.4 CPU seconds
and 1,054,568 KiB RSS for the gate. Current source hashes are matched to actual
successful native rows in `SOURCE-NATIVE-COVERAGE.json.gz`.

Initial memory-admission refusals and one failed imported-namespace inspection
are preserved as failed attempts. In that inspection attempt, the two exact
aliases and their own namespace audit had already passed; enumerating the
imported candidate namespace failed. The repair changed only inspection
commands to print all eight named imported theorem dependencies explicitly.
The candidate's own eight-theorem audit and the aliases' two-theorem audit
remain intact. No mathematical proof bytes were repaired or weakened.

See `ACCEPTANCE.json`, `AXIOMS.json`, `PROOF-AND-SOURCE-REVIEW.txt`,
`ATTEMPTS.json`, the exact native logs and losslessly compressed original
receipts. `EVIDENCE-ENCODINGS.json` records stored and uncompressed hashes.
No fresh full-root build or remote-CI pass is claimed.

The supervisor paused after this R001, with all jobs reaped and author/compiler
guards paused. No R002 or automatic restart is authorized. The user separately
authorized publication of this checked checkpoint on the existing cumulative
branch. Publication changes no proof, dependency, toolchain or CI policy.
