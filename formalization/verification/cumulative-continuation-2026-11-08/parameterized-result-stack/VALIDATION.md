# Validation record

The eight-target freeze was independently accepted without amendments.
Its manifest SHA-256 remains:

`334de384f2395c0fcd94cee5dc6c4220a0383a75369dff40b3749434fce14f92`

Comparator-only native preflight passed before proof authorship. The final
`InternalParameterizedApplicationResultStackStatementChecks` module directly
checks one theorem against each frozen target and prints its actual axiom
closure. Every own proof namespace additionally runs `#audit_namespace`.
The eight aliases and all 53 audited declarations use only the permitted
standard axioms. There are no current-component compiler warnings.

The final exact gate passed in immutable receipt
`build-reports/1794154302557301972-17.json`. The preflight receipt is
`build-reports/1794153752162790670-6.json`. Their hashes are recorded in
`ACCEPTANCE.json`. `exact-checks.log` contains the source-matched exact alias
and namespace audit output.

The noncompiler collector verifies:

1. Every one of the 1,165 current local imports matches a successful row
   from an immutable numeric native receipt and a corresponding hashed log.
2. Every used receipt has the unchanged bounded single-thread profile.
3. Every frozen file and all original supplier/input pins remain unchanged:
   1,186 pins, including all 1,178 broader frozen Lean inputs.
4. Those broader Lean inputs also have successful current-source native
   matches, even when they are not needed by the final focused import graph.
5. Failed module rows are never accepted. A source-matched successful row
   remains valid when a later module in the same checker run failed.
6. Every new proof namespace and all exact aliases has its actual axiom
   closure audited; no `sorryAx` dependency or new axiom is accepted.

The source-to-receipt maps, receipt copies, attempt logs, collector and
resource summaries are retained locally. `CLOSURE-SOURCE-PINS.json` is the
portable current import-closure manifest. Native build receipts and objects
are not substituted for proof sources and are not needed by public imports.
The portable packet contains the twelve new Lean files and scoped evidence,
without changing existing supplier bytes.

The focused gate is not a new aggregate build of the full package, a remote
CI claim, a parameterized append/framing theorem, or full fold correctness.
The original paper06 source register and all excluded claims remain unchanged.
No resource limits were raised to repair compiler errors. Seven unsuccessful
attempts are retained; repairs concerned ordinary proof elaboration and
argument-vector syntax, never a frozen target or source definition.
