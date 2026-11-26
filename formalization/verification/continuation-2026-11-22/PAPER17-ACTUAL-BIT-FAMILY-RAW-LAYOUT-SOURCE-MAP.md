# Paper 17: literal serialized bit-row family and executable ordered source namespace

Printed source: `arithmetic.tex`, finite matrix language and residues,
finite strips, and one-variable projection in `thm:arithmetic`.

- Encode each existing signed raw row by its existing literal row code
  and keep the exact intended Boolean bit separately. Preserve row and
  clause order, duplicates, test codes, coefficients and all operand
  positions, including zero and mutually cancelled weights.
- Read coordinates from the raw rank field of each original operand
  in its occurrence order. On these same raw names compute a sorted
  duplicate-free index by enumerating up to the true finite maximum
  and retaining just the names that appeared. This is primitive recursive
  even on arbitrary byte-shaped raw families, with no validation claim.
- On literal encodings this exact index has the same coordinate set and
  cardinality as the typed family. No equality with the arbitrary
  enumeration order of `Finset.toList`; no coefficient-grouping, raw
  chart congruence, raw compiler, low execution, or closed solver claim
  in this first bridge.
