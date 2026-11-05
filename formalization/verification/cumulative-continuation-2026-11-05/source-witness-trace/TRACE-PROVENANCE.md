# Original positional traces and exact computation

The trace follows only the original leading existential constructors. It retains
one value per position, including duplicate binder names. The updateTrace target
records sequential Function.update semantics and the exact residual formula.
The residual can still contain binders and Booleans; no prenex or quantifier-free
claim is made.

Each actual step uses the checked globally total least-witness program on the
current table and original body code. Recursive code calls use the exact updated
table and strictly smaller original body code. The finite graph may include a
child for an existential node even before its admission guard is inspected; an
unsupported assembler ignores child values. This is a computation proof for the
frozen function, not an execution-cost assertion.

Recursive leastRealization means each selected value is the least assignment
with a satisfying continuation and the suffix is chosen in the resulting current
environment. Its semantic existence lemma uses ordinary natural well-ordering;
actual numeric effectivity is proved separately from the concrete graph and
already checked witness program. No external witness/termination oracle is used.
