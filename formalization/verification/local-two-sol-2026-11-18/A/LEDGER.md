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

## 2026-11-18 20:09 UTC — Paper16 lem:operator numbered gate passed

`MarkedConstructorOperatorChecks.exact_Operator` passed core gate
`1795032562986279741-56`. The 170-module recursive evidence, five
exact axiom audits and 37 frozen hashes are in [OPERATOR-EVIDENCE.json](OPERATOR-EVIDENCE.json),
SHA-256 `3b1ca4f7653940f81d955fce090e436d0c6b2cb608efa8c4a961667afcb70f3e`.
The numbered operator uses the literal ordinary-input inventory, discharges
prefix closure, encodes the actual new marked value at every valid family
coordinate, preserves the coherent carrier, and is monotone on all retained
families. Bottom iteration stabilizes at the explicit finite bound and
is below every retained fixed point.

The source lookup calibration companion is frozen in
`LANE-A-OPERATOR-LOOKUP-FROZEN.json` and is undergoing its own gate. It
checks concrete source-inventory lookup and validity for Select and Copy/Stat,
and the real canonical observation extension, opened observation and output
lookup for FAbs. It uses the same operator definitions and source inventory.

## 2026-11-18 20:12 UTC — Paper16 lem:operator READY-FOR-ROOT-REVIEW

Final core union receipt `1795032756929340478-76` passed the numbered
`exact_Operator`, `exact_SourceLookup`, and all twelve frozen constructor
aliases. [OPERATOR-FINAL-EVIDENCE.json](OPERATOR-FINAL-EVIDENCE.json) reconciles
197 current source-matched modules, 14 standard-only axiom audits and 37
frozen hashes. Its SHA-256 is
`3e6cdf3774a9dc306c5845133619d70c6cd1a8c50bb8a26d3f292c85a6a61f20`.

The complete operator packet consists of the frozen
`MarkedConstructorOperator` and `MarkedConstructorOperatorTargets`, the leaf
modules `MarkedConstructorInventoryProof`, `MarkedConstructorEncodingProof`,
`MarkedConstructorEndomapProof`, `MarkedConstructorIterationProof`,
`MarkedConstructorStabilizationProof` and `MarkedConstructorOperatorChecks`,
and the source-lookup companion. The companion is
`MarkedConstructorSourceLookupTargets`, `MarkedConstructorSourceTupleProof`,
`MarkedConstructorCanonicalOpeningProof`, `MarkedConstructorSourceOpeningProof`
and `MarkedConstructorSourceLookupChecks`. It derives same-owner retyped
full tuples from the literal head/type inventory, retained owner lookup for
every observed target head argument, and the canonical FAbs port extension
and actual opened observation with a retained output. All preservation and
stabilization laws range over the full retained coherent family carrier.

The compiled packet awaits independent root review. Failed draft sources are
preserved under receipt-named paths in `paper16/failed/` and in their original
locations for the inherited drafts. Register adoption remains with root.

The next target is `lem:structural-interpretation`. First freeze the actual
ordinary-head, lambda, and protected original-spine helper equations with
the constructor-first builder. Prove the mutual Expr/Args/nonempty helper
recursion on original syntax, including protection reset at an empty residual
and the one full application on an unprotected supplied value. Then prove value
validity, weakening, capture-avoiding substitution and concrete full-call
correspondence, including original undefined cases.

## 2026-11-18 20:14 UTC — Operator acceptance-schema evidence

[LANE-A-OPERATOR-EVIDENCE.json](../../new-paper-set-2026-11-18/paper16/LANE-A-OPERATOR-EVIDENCE.json)
is the acceptance-schema export for receipt `1795032756929340478-76`.
SHA-256 `3be74618feb6ce254ed4518b68e552b52123ff35f64a4483667d9a9adf4c1a33`.
It uses top-level `modules` records with `source_sha256` and `outputs`, and
also pins each native receipt and proof log. This export covers all twelve
builder aliases, so it supersedes separate acceptance-schema exports of the
constructor tests, validity, and monotonicity. The original A/ evidence files
are retained. Future ready packets will include this export beside the
original evidence and will continue directly to the next proof.

## 2026-11-18 20:19 UTC — Interpreter environments READY-FOR-ROOT-REVIEW

The frozen environment targets `Weakening`, `EnvironmentComposition`,
`CodeLookup` and `LookupWeakening` passed core receipt
`1795033114927873028-61`. The acceptance-schema evidence at
[LANE-A-INTERPRETER-ENVIRONMENT-EVIDENCE.json](../../new-paper-set-2026-11-18/paper16/LANE-A-INTERPRETER-ENVIRONMENT-EVIDENCE.json)
has SHA-256 `bd34b77f53a46063adcfadc250adbf3edb77cf115821287152932bc5eccff9ab`.
The [original evidence](INTERPRETER-ENVIRONMENT-EVIDENCE.json) has SHA-256
`787b6f20256179ac995d3e6c06211785a5efc3dbf63f94074a64d1525a5f8806`.
Both cover 104 modules, four exact aliases and 31 frozen hashes.

`ProtectedSpineEnvironmentTargets` specifies the typed finite environment
laws, with proofs in `ProtectedSpineEnvironmentWeakeningProof`,
`ProtectedSpineEnvironmentLookupProof` and `ProtectedSpineEnvironmentNaturalProof`.
Actual literal-variable and whole-bottom fallback codes remain retained and
restrict correctly. The original-syntax interpreter definitions also compiled.
The next gate preflights the frozen `ProtectedSpineLaws` comparator and
the next proof combines the variable, constructor, and lambda cases.

## 2026-11-18 20:41 UTC — Interpreter and helper laws READY-FOR-ROOT-REVIEW

The exact `InterpretationLaws` supporting comparator passed together with
the four environment aliases in core receipt `1795034452188903357-21`.
The acceptance-schema
[LANE-A-INTERPRETER-LAWS-EVIDENCE.json](../../new-paper-set-2026-11-18/paper16/LANE-A-INTERPRETER-LAWS-EVIDENCE.json)
has SHA-256 `01008f06df4dea30bb7bed2c564ae1b7ce5d4d754acb8fcc0ce1f54e1130e668`.
The [A/ evidence](INTERPRETER-LAWS-EVIDENCE.json) has SHA-256
`914a04091fefed1441b614a62c5aba6348aa592e8bf43ecfdfcf99ba1dcaab20`.
There are 204 source-matched modules, five standard-only audits and 46
frozen hashes. The qualified freeze adds an import for the unchanged
comparator; the first target draft is preserved.

The proof uses the original mutual Expr/Args recursors after the attempted
well-founded proof reached the resident-memory cap. The actual evaluator
and protected helper are unchanged. For every typed covered expression and
valid environment, value and call outputs are hereditary, monotone and
natural. The lambda proof uses the same descendant port choice and proves
membership of the actual opened observation. Its two tuple branches preserve
the consumed index count on continuation and reset the call on an empty
residual. Ordinary and marked heads use the same actual constructor tables.
The numbered `lem:structural-interpretation` still needs capture-avoiding
substitution and concrete application correspondence. The next packet is
scoped environment/protection agreement and substitution of concrete images.

## 2026-11-18 20:42 UTC — Scoped evaluator agreement READY-FOR-ROOT-REVIEW

Frozen `ScopeAgreement` passed core receipt `1795034545832105513-58`.
The acceptance-schema
[LANE-A-INTERPRETER-SCOPE-EVIDENCE.json](../../new-paper-set-2026-11-18/paper16/LANE-A-INTERPRETER-SCOPE-EVIDENCE.json)
has SHA-256 `83bc53afc903f7dd61773d70223c79ae8b0cbf2d394a1825939c9674aeb92939`.
The [A/ evidence](INTERPRETER-SCOPE-EVIDENCE.json) has SHA-256
`bafdcd43566de3957917aa5e15689b02cc4783213db46c1d018def8d730bc10c`.
The gate reconciles 212 modules, one standard-only exact audit and 48
frozen hashes.

`ProtectedSpineScopeAgreementProof` proves agreement of the actual interpreter
and helper whenever free lookups, well-scoped bound lookups and the relevant
original protection tests agree. The bound-tail independence for a closed
concrete image follows from the empty bound context. The next packet uses
this result for full-table use of a substituted free variable and carries
capture-avoiding substitution through the actual original source syntax.

## 2026-11-18 20:50 UTC — Free substitution and application counterexample READY-FOR-ROOT-REVIEW

Core receipt `1795034969148656801-17` passed `exact_FreeSubstitution`,
`exact_AvailabilityGap`, `exact_ScopeAgreement` and
`exact_InterpretationLaws`. The acceptance-schema
[LANE-A-INTERPRETER-FREE-AND-GAP-EVIDENCE.json](../../new-paper-set-2026-11-18/paper16/LANE-A-INTERPRETER-FREE-AND-GAP-EVIDENCE.json)
has SHA-256 `1d0e9852122554920e812296f0e8712957459a9e76b7639510ad9e9790b04e76`.
The [A/ evidence](INTERPRETER-FREE-AND-GAP-EVIDENCE.json) has SHA-256
`dc70754fc868d5bd1adba99162fb283b0d59673822f329549ebfe4590e2a8e35`.
The union covers 232 modules, four standard-only audits and 50 frozen hashes.

`ProtectedSpineSubstitutionTargets` and the free-input, free-variable,
free-case and free-substitution proof modules compare the actual capture-
avoiding `freeSub` with interpreted images across all descendant contexts.
The free-variable case derives equality with the concrete image's original
full table, including the image's own original protection behavior.

The complete same-family application-equality reading of the numbered
structural interpretation statement is obstructed. The frozen
`ProtectedSpineApplicationCounterexampleTargets` and
`ProtectedSpineApplicationGapChecks` prove the gap for ordinary successor
applied to a covered ground variable. Both query inputs are ordinary and
signature-valid at the same arrow type. At their actual bottom constructor
family and valid root context, the helper has false availability. The
literal syntactic call succeeds and its marked result has true availability
when interpreted at that same family. This is a code inequality witnessed
by the decoded availability bit. The operator and support laws still pass.

Next, prove bound substitution and a genuine fixed-point application supplier
for adequacy. The numbered structural statement's arbitrary-family
correspondence remains open for source review.

## 2026-11-18 20:54 UTC — Bound substitution READY-FOR-ROOT-REVIEW

The frozen `BoundSubstitution` target passed core receipt
`1795035232891684905-37`. The acceptance-schema
[LANE-A-INTERPRETER-BOUND-EVIDENCE.json](../../new-paper-set-2026-11-18/paper16/LANE-A-INTERPRETER-BOUND-EVIDENCE.json)
has SHA-256 `12ded5b77ecded9973242470b0121dcbf9bd1f50b469a5c7cbc36de9a49f2239`.
The [A/ evidence](INTERPRETER-BOUND-EVIDENCE.json) has SHA-256
`f9ae3e59af52b64ea3e54ed7d1702e49e5a46b888558a01b7312029e85ef80f2`.
The report reconciles 227 modules, the standard-only exact alias and 50
frozen hashes.

The bound-input, bound-variable, bound-case and bound-substitution proof
modules use the literal simultaneous `substitute` operation. The
environment relation preserves the retained binder prefix and reads
concrete codes for the removed slots. Helper agreement keeps both protection
counts inside the retained prefix, so replacement of a removed slot uses
its genuine full table. This supplies the concrete empty-residual and
functional-argument interpretation needed for the fixed-point application
proof. The latter has a separately frozen comparator and passed preflight.

## 2026-11-18 21:00 UTC — Fixed-point concrete application READY-FOR-ROOT-REVIEW

Core receipt `1795035582102039377-12` passed
`exact_FixedApplication`, `exact_FixedApplicationAux` and
`exact_BoundSubstitution`. The acceptance-schema
[LANE-A-FIXED-APPLICATION-EVIDENCE.json](../../new-paper-set-2026-11-18/paper16/LANE-A-FIXED-APPLICATION-EVIDENCE.json)
has SHA-256 `8be54cba8e91a213e5bfbd9dc492e12d3383b2d40bc3af0f2e8ea5903c073619`.
The [A/ evidence](FIXED-APPLICATION-EVIDENCE.json) has SHA-256
`462dc915d73f9316e3859b1a08af9d9f554b6bf98e9962070dc5b2f8be3e1a8b`.
The report reconciles 237 modules, three standard-only exact aliases and
50 frozen hashes.

`ProtectedSpineFixedApplicationTargets` fixes the actual typing, bound
images, full tuple and `applyAux` result. The proofs preserve the original
consumed prefix, use the entire bottom when the original call fails, and
encode the actual substituted syntax when it succeeds. The successful
functional branch uses equality of the previous family and the checked
operator output at a fixed point. This supplies the successful full-call
lookup for fixed-point adequacy. The same-family counterexample at bottom
remains the boundary for the numbered structural statement.

The next packet calibrates the actual strict bit against successful marking
and translates the existing canonical-port derivations into fixed-point bits.
