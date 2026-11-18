# Lane A ledger

## 2026-11-18 19:46 UTC — Constructor test and lookup packet started

The frozen comparator is `MarkedConstructorTargets.lean` with the 30-file
manifest in `paper16/MARKED-CONSTRUCTOR-FROZEN.json`. The first targets are
`MatchingExact`, `MultisetExact`, `CopyExact`, `StatExact`, `SelectExact`,
`FAbsExact`, `Fields` and `TupleSuccess`. The inherited proof drafts are
preserved. New leaf proofs and aliases audit the literal builder fields and
the successful appended-owner tuple lookup. Scope is constructor support for
the printed structural interpretation and operator lemmas.

## 2026-11-18 19:56 UTC — Constructor tests READY-FOR-ROOT-REVIEW

Frozen targets `MatchingExact`, `MultisetExact`, `CopyExact`, `StatExact`,
`SelectExact`, `FAbsExact` and `Fields` passed core gate
`1795031766013559319-80`. The 43-module recursive evidence and all seven
exact axiom audits are in [CONSTRUCTOR-TESTS-EVIDENCE.json](CONSTRUCTOR-TESTS-EVIDENCE.json),
SHA-256 `4e35529abb00a8432dae55baf53485ba07508913e1556639ea75b2eca58422d7`.
All 30 frozen hashes match. Axioms are within the standard whitelist.

Paper16 modules are `MarkedConstructorOccurrenceChecks` (inherited proof),
`MarkedConstructorHeadExactProof`, `MarkedConstructorTestChecks` (inherited
Select proof and new `MarkedConstructorFAbsExactProof`), and
`MarkedConstructorFieldsProof`. Earlier Head and FAbs source files stay at
their original paths. The failed lane drafts are saved under the corresponding
receipt IDs in `paper16/failed/`, with gate output in this ledger directory.

The results establish the four actual Boolean test/witness equivalences,
positional matching and replacement, availability, and the literal shared
weak/strict field equation. The next packet checks `TupleSuccess`,
`Coherent` and `ValueValid`, using actual retained-family outputs and
inserted-extra weakening. Input and family monotonicity follow as a separate
packet. The numbered statements remain pending.

## 2026-11-18 19:59 UTC — Constructor table validity READY-FOR-ROOT-REVIEW

Frozen `TupleSuccess`, `Coherent` and `ValueValid` passed core gate
`1795031949814546425-56`. The 123-module recursive evidence and standard-only
axiom audits are in [CONSTRUCTOR-VALIDITY-EVIDENCE.json](CONSTRUCTOR-VALIDITY-EVIDENCE.json),
SHA-256 `1bea70e61eaf97805fa16740444c31f74683834f00eac9e31a8f811ddcabcbf9`.
All 30 frozen hashes match.

Files include the inherited `MarkedConstructorTupleProof` with new
`MarkedConstructorTupleChecks`, and the new `MarkedConstructorParameterProof`,
`MarkedConstructorCoherentProof`, `MarkedConstructorTagOrderProof`,
`MarkedConstructorAppendProof` and `MarkedConstructorValidityProof`.
Complete full-prefix tables have successful old-family lookups, retained
outputs, tuple monotonicity and actual restriction naturality. Coherence
compares the exact same descendant coordinates and uses actual positional
and downset restriction composition. The explicit `PrefixClosed` inventory
interface remains on the frozen contracts. Next are `InputMonotone` and
`FamilyMonotone`, which additionally require transport of every successful
Select, Copy, Stat and FAbs witness.

## 2026-11-18 20:04 UTC — Constructor monotonicity READY-FOR-ROOT-REVIEW

Frozen `InputMonotone` and `FamilyMonotone` passed core gate
`1795032241009033322-28`. The 159-module recursive evidence, both exact
axiom audits and 34 frozen hashes are in
[CONSTRUCTOR-MONOTONICITY-EVIDENCE.json](CONSTRUCTOR-MONOTONICITY-EVIDENCE.json),
SHA-256 `e82c04f9fa2dcfe45d8e2982b449a88b66b7b7e67b458b64e05885e8d3883092`.

The new leaf modules transport Select by typed positional tags and complete
same-owner tuple lookups, Copy through all whole-owner bits, Stat through its
original positional split and occurrence matching, and FAbs at the same
coordinate-local port. The code order proofs recover the actual observation
from a true decoded bit and use successful lookup, carrier membership and
order throughout. FAbs input order derives the extended context and retained
literal port value. The tuple laws use actual previous-family output order.

All twelve supporting builder aliases now have native gates and evidence.
The fresh numbered `lem:operator` comparator in
`MarkedConstructorOperatorTargets.lean` preflighted in the same gate.
Its source map and 34-file freeze are under paper16 as
`LANE-A-OPERATOR-SOURCE-MAP.md` and `LANE-A-OPERATOR-FROZEN.json`.
Next are actual family encoding, endomap coherence and stabilized bottom
iteration at the literal ordinary-input inventory.
