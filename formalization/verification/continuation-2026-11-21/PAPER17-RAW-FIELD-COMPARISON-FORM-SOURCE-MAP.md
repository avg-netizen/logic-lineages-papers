# Paper 17: exact raw compiler for the existing comparison forms

**Target-only supplier.** No proof, new native evidence, or numbered credit.
Record 704 and supporting checked records 712 and 714 are unchanged.

Printed source: arithmetic.tex, ordinary-field syntax and
`lem:field-comparison`, principally the requirement for an effective finite
Boolean form in which a nonlinear comparison parameter uses only the smaller
coordinate. This packet isolates executable generation of the old forms,
not their full printed domain.

- Uses the literal 714 `LongFieldCode` tuple (tag, exponent, two endpoint
  raw codes). Distinct output is tagged constant or tagged linear
  sign plus an exact field tuple. No parameter substituting unrelated
  syntax, no oracle, no evaluation of that field or choice of coordinate
  inside the compiler. The existing form interpretation reads that
  parameter on the smaller input.
- Distinct ordered input uses the actual four old cases: iterate/iterate
  coefficient cancellation; iterate/entry fixed less; entry/iterate
  cancellation or advance by `ω*(b-a)`; entry/entry advances both
  endpoints, compares `dq` to `dp`, and in the less branch uses the
  original certificate at `dq` and the exact partner endpoint `mp'+dq`.
  Both strict and equality row behavior is inherited only in later
  semantic assembly, not asserted by this syntactic packet.
- Same raw coordinate uses ordinary numerical exponent order, fixed mixed
  orientation, or raw comparison of `dp` against `dq` (the opposite
  ordering from the distinct-order test). Equality uses the original
  certificate at `dp`. Ordinal sum/subtraction, omega monomial, comparison
  and equal-gap sign are the actual existing numeric notational algorithms.
- Uniform primitive recursion on every code is required. Input tag zero is
  iterate, other tags are processed as entry; no normalized or semantic
  input promise is made for arbitrary malformed code. Calibration is on
  codes of real `ValueField` terms. It requires exact encoded output and
  round-trip raw trees, not just ordinal equality or equisatisfiability.
  Syntactic calibration on short fields deliberately gives no old-form
  semantic correctness there.
- Later work: combine the raw compiler with accepted short preprocessing
  and effective LongField tails; cover same, strict and reversed order on
  the all-large branch. Proper parameter fields can reuse 704's
  `FormWellFormed` on LongField inputs. Exact below-cutoff hit/miss
  evaluation, mixed low/high strips and concrete cancellation remain
  separate.
