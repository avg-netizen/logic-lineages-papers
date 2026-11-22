# Paper 17: literal encoded shared rank renaming on ordered signed-bit families

Printed source: `arithmetic.tex`, identification of equal raw coordinates
and strict base-order branches in `thm:arithmetic`.

- Compute the same original first matching name-to-rank lookup, with
  the original code default outside the chart. Replace only the rank
  field of each literal raw operand; retain every row and operand in
  its original clause/row order, including duplicates and zero or
  cancelled weights. Test/modulus, coefficients, constants, intended
  bits, field tags and ordinal/iterate payload are copied unchanged.
- Calibration is exact equality with the encoded existing typed
  ranked family for every chart and every literal source family. The
  raw operand occurrence tape is exactly the original occurrence
  tape mapped by the same chart lookup.
- The code is primitive recursive on charts and arbitrary byte-shaped
  families. It does not validate raw input, compare ordinal meanings,
  or make its default a proof of read availability. On genuine charts
  actual coordinate scope, ties and value transport are separate
  typed interface conclusions.
- No effectivity of cutoffs, pruned short/long syntax, grouped
  weights, signed route generation, high projection, or closed
  solver; no numbered promotion.
