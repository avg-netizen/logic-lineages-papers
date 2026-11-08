# Checked original path checkers and internal path lifting — 7 November 2026

The focused module `LogicLineages.ExternalCheckpoint20261107PathChecker`
passed with **13 new exact supporting targets** in three components. The
numbered register remains **168 checked, 2 inherited and 19 pending / 189**.
Paper06 `lem:id1` retains its pending status.

| Component | Exact targets | Completed result |
|---|---:|---|
| Original quotient-edge checker | 5 | Actual primitive Program witnesses, exact all-input `numericEdgeTest` calibration, and internal acceptance decomposition/reconstruction at original certificate fields and representative graph outputs |
| Original path checkers | 6 | Concrete reflexive/positive checker ASTs, exact all-input calibration, and internal nil/cons acceptance equations |
| Internal application path lifting | 2 | Reflexive and positive acceptance preserved by the literal application path map, internally proved from local arithmetic invariant propagation and single-edge compatibility |

## Mathematical progress

The quotient-edge checker is an explicit composition of the original
certificate selectors, step checker, representative builders, equality test,
and exact-one conjunction. Its source builder uses the original universe
decoder; its target builder uses the original packed-term decoder without an
extra universe filter. Failure of either decoder already forces the original
step checker to reject. This gives calibration on every natural input,
including malformed codes and windows that are not subtype closed.

Its internal equations recover the actual step acceptance and representative
graphs at the supplied endpoints. At supplied representative outputs they
recover exactly the two endpoint equalities. The converse derivations rebuild
acceptance, including when the certificate is supplied by the original
nested-pair constructor. These are original arithmetic graph derivations for
arbitrary symbolic terms and contexts; calibration supplies no internal
derivation premise.

The path component gives explicit Programs for the original reflexive and
positive tests. The concrete list recursion retains the current source
vertex of each suffix. Its internal equations identify reflexive acceptance
of nil with endpoint equality and prove rejection of nil by the positive
checker. On an original pair-coded cons entry, both checkers expose the head
edge and the reflexive accepted suffix. Their numerical calibrations retain
the unchanged original path decoder, edge test, and positive test on every
raw natural code.

The generic path-lifting result now proves the internal traversal argument
for the literal `InternalApplicationPathMap.pathMap`. It retains the four
original context/domain/codomain/argument parameters, both supplied vertex
graph outputs, the supplied mapped certificate graph output, and every
ambient hypothesis. Reflexive and positive acceptance are both preserved
from two explicit local families of closed arithmetic derivations:

- The arithmetic source invariant propagates across a single accepted edge.
- One accepted edge, the source invariant, the two vertex graph witnesses,
  and the actual original `edgeLift` graph imply acceptance of that exact
  lifted certificate between those exact vertex outputs.

Original full-language list-code induction proves a row quantifying both
endpoints, their vertex outputs, and the mapped certificate. Program totality
supplies the six entry and mapped-tail witnesses; the original constructor
and map equations identify their actual outputs. The cons step propagates
the arithmetic invariant, lifts one edge, and applies the internal tail
hypothesis. Positive acceptance excludes zero internally and yields genuine
cons witnesses, allowing the same reflexive tail induction to apply. Every
auxiliary witness is eliminated inside the original calculus.

The generic theorem therefore derives path preservation from local rules.
The concrete source-specific local rules remain separate proof obligations.
The accepted source correspondence records this boundary in
[the path-lift component](../internal-application-path-lift/SOURCE-CORRESPONDENCE.md).

## Acceptance

All three exact gates and the focused aggregate passed. The closure contains
**1,225 local source modules** matched to successful native receipts. The
checkpoint records **25 new Lean files**, including the aggregate module.
All 13 actual axiom closures are contained in `propext`, `Classical.choice`,
and `Quot.sound`. Every accepted definition and target matches its frozen
record; existing proof and definition files are unchanged.

The pinned Lean `v4.32.0-rc1` and Mathlib revision
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` are unchanged. The serialized profile
uses one worker, a 2,048 MiB heap cap, a 1,536 MiB process-tree RSS cap,
a 2,048 MiB free-memory floor, and the existing 90-second CPU / 180-second
wall limits per compiler. Peak successful observed RSS was **1,262,484 KiB**.
No full public-root build or remote CI result is claimed.

[ACCEPTANCE.json](ACCEPTANCE.json) records the exact gates, source hashes,
frozen-specification checks, and resource profile. The three final gate logs
are retained alongside it. UTC receipt timestamps remain their actual
timestamps; this continuation is filed under 7 November 2026.

## Remaining source obligation

The next concrete requirement is the internal original application-step
rule with its typed endpoint guards, together with the representative
congruence derivations needed by the exposed quotient-edge equations. An
explicit arithmetic invariant must carry the original window, typing, and
fixed-argument conditions, and both local rules must be proved for that
same concrete source package.

Joint-context assembly and the outer `ApplicationCertificateLiftPath.pathValue`
object decoder, same-context conditions, and malformed-object fallback still
require their original treatment. Fixed-Gamma all-input calibration and the
generic internal path theorem do not discharge those wrapper obligations.

The full finite-type downward-closure consumer remains conditional on
`CertifiedApplicationLift`. The source multiset singleton/union,
constructor, lambda, computable-substitution fundamental argument, and the
closed all-term derivation at
`ContextUniformTargets.ActualContextUniformInternalAccessibility` remain
unfinished. No numbered source statement is promoted by this checkpoint.
