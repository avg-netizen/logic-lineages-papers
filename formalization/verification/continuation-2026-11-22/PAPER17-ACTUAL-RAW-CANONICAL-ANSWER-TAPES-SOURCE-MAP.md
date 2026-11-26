# Paper 17: executable finite ternary answer tapes on the original canonical label pairs

Printed source: `arithmetic.tex`, branch on the finite
whole pattern of full-value comparisons during signed normalization.

- Emit candidate codes in the exact same order as the original
  typed finite patterns: less (0), equal (1), greater (2), each
  prefix followed by every previous shorter tape in order. Literal
  equality is with the entire encoded list, not only membership.
  Each emitted tape has the requested length and only ternary codes.
- Apply the exact canonical active label tape and its own Cartesian
  pair width (label count squared), preserving the actual original
  label and pair layout. As a consequence, after literal canonical
  grouping the raw output is exactly the typed candidate tapes on
  that same order. No equality with arbitrary legacy Finset order.
- This primitive recursive generation neither evaluates actual
  comparisons nor asserts any candidate is true or guard-feasible.
  No read success, packet guard rendering, route/trace compiler,
  high branch completeness, or numbered promotion.
