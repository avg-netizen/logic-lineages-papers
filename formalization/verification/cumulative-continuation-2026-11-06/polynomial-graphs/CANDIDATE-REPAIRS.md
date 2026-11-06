# Candidate checks and repairs

Frozen definitions and exact target propositions remain byte-for-byte unchanged after the successful preflight. The initial malformed binder spelling and its unsuccessful preflight are retained under `preflight/`. Every tested candidate source is retained by hash under `candidates/`, and native receipts and logs are retained byte-for-byte by the evidence collector.

The native checks found only local elaboration and proof-normalization issues:

- The preflight binder used Lean's reserved lambda token; it was renamed before any candidate proofs were authored.
- Word degree monotonicity needed explicit case simplification in both the hypothesis and goal.
- Head code calibration needed explicit instances of the existing norm-code correctness theorem beneath list maps.
- The symbolic-row calculation needed the induction equality rewritten before normalizing negated products.
- Two primitive-recursive tuple expressions needed complete tuple parentheses before their type annotations. Repeated unsuccessful checks of these annotations are retained.
- Call-list count arithmetic needed its local kernel-input abbreviation unfolded, and singleton letter membership was eliminated explicitly before proving degree bounds.
- Support proofs retained named equalities instead of allowing substitution to remove a name referenced later in the proof.
- Appended row satisfaction was proved by direct list membership, avoiding an unfinished conjunction reassociation.
- The head norm helper now specializes the already accepted finite-monomial norm theorem through its explicit defining-module import; the original notation-normalization candidate is retained.

These changes affect proofs only. They do not change source functions, domains, degree bounds, graph exceptions, variable correlation, target quantifiers, axioms, compiler limits, or dependencies' source bytes.
