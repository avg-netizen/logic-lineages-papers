# Application dynamics and the literal common-knowledge counterexample

Continuation of `206a3ae00217a77830595afe6285461553b58802` on
`formalization/cumulative-continuation-2026-11-16`.

## Source checkpoint status

The three target/comparator pairs passed independent preflight review and
native comparator checks before proof authoring. All candidate proofs have
passed independent source review. Their final native proof gates and the
installed-source dependency recheck are pending at this source checkpoint.
No candidate proof is adopted by this status statement. The later acceptance
record, when present, supplies the completed native and evidence results.

## Paper 6: original raw application dynamics

`RawApplicationDynamics` treats the unchanged, typed original `RawStep` and
`RawSteps` relations. A finite path from `app f a` ends at bottom, remains an
application after a path in `f`, or reaches a lambda in `f`, takes its beta
step with the original argument, and follows an arbitrary suffix from that
exact substitution result. The equivalence includes all three alternatives.

The accessibility criterion is exact: `app f a` is accessible if and only if
`f` is accessible and every beta contractum obtained from a lambda reachable
from `f` is accessible. The source relation reduces only the function side
of auxiliary applications. No argument-accessibility premise or generic
substitution-stability assumption is added. The two exact contracts have a
23-module local closure and reuse the preceding raw-lambda packet.

## Paper 12: the displayed sentence's own common-knowledge code

`LiteralCommonKnowledgeCounterexample` uses the literal formula

`theta = (allAgentsKnow falseEquality -> falseEquality)`.

It transports the previous chosen-common-knowledge equivalence to derive the
literal CK collapse at the same `Actual` tuple, installed fixed-point family,
and internal HB2/HB3 proofs. The literal sentence and the selector-guarded
helper keep their distinct syntax and codes.

For each value of the original optional-UBF flag, the exact contract includes:

- a proof of the literal theta;
- a proof of the negation of its chosen common-knowledge sentence;
- a proof of every external finite selected iteration of theta;
- nonprovability of that common-knowledge sentence.

The optional-UBF extension is handled by a structural embedding of all six
original proof constructors. Nonprovability invokes existing consistency for
the same actual tuple and flag; the target adds no consistency premise.

This small 300-module packet has three exact contracts, including an explicit
consumer of `SelectedCertifiedPresentation`. Its antecedent is retained.

`SameSourceLiteralCounterexample` supplies the separate unconditional source
endpoint. It invokes `SameSourceOriginalAdoption.Proof.originalSelected` once
and retains all its witness fields: actualness, syntax adequacy, code program,
registry installation, fixed-point family, and internal HB2/HB3. Every literal
conclusion concerns that same tuple. Its final gate has a 2,905-module local
closure. Acceptance requires native verification of this complete focused
Paper 12 dependency closure in addition to the small logical consumer.

## Verification and scope

`FROZEN.sha256` pins 23 specifications, suppliers, register and build inputs.
The packet-specific `FROZEN-COMPARISON.json` and `REVIEW-PREFLIGHT.md` records
identify the exact contracts frozen before proof authoring. The provisional
false-only Paper 12 targets are preserved under
`literal-common-knowledge/provisional-false-only/`; the reviewed final target
quantifies over both original theories.

`COMPARATOR-CHECKS.json` records both successful preflight receipts.
`SETUP-ADDITION.json` records the three additional official pinned Mathlib
cache roots. The portable `ordered_check.py` expands only a requested local
dependency closure into dependency-first roots before invoking the unchanged
native checker. This avoids Python scanner recursion depth for the installed
witness. Its independent review is in `REVIEW-ORCHESTRATION.md`.

All native proof checking uses one compiler thread, a 2,048 MiB heap limit,
a 1,536 MiB process-tree RSS limit, a 2,048 MiB free-memory floor, and per-module
90-second CPU / 180-second wall limits. The checker, toolchain, dependency pins,
CI and manuscripts are unchanged. No full Paper 6 or aggregate-root build is
part of this checkpoint.

The numbered register remains **178 checked, 2 inherited, 9 pending / 189**.
These are supporting raw-reduction results and the literal unnumbered Paper
12 source counterexample. Full Paper 6 context-uniform accessibility and its
remaining internal certificate/quotient obligations remain pending, as does
Paper 2's broader consumer statement.

## Focused reproduction

With the pinned toolchain and official dependency cache installed, run from
`formalization` using a writable shared `LEAN_CHECK_LOCK_DIR`:

```sh
python3 verification/continuation-2026-11-17-application-literal/ordered_check.py \
  LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.StatementChecks

python3 verification/continuation-2026-11-17-application-literal/ordered_check.py \
  LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.StatementChecks

python3 verification/continuation-2026-11-17-application-literal/ordered_check.py \
  LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLiteralCounterexample.StatementChecks
```

The first two gates are independently useful focused targets. The third pays
the larger installed-source dependency closure; it is a separate native check.
