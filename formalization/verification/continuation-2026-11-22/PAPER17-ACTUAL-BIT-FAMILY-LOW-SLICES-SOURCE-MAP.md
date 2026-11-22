# Paper 17: actual finite signed-bit families, exact low strips at one shared source digit

Printed source: `arithmetic.tex`, `thm:arithmetic`, dimension decrease on
the whole infinite strip of a selected actual low coordinate.

- For one chosen source coordinate and one supplied value, slice every
  row of every candidate using its actual original field reader.
  Collect rows only if every actual status is a genuine hit; invalid and
  genuine miss are not Boolean false and give no candidate.
- Reattach every original ordered intended row bit to its same surviving
  row and exact constant, preserving bit order and source-row multiplicity.
  Exact actual ordered snapshots preserve and recover the same signed
  predicates at the very same updated valuation.
- The finite low family enumerates one shared digit per child, with all
  remaining raw coordinates unbounded and prior evaluated at that
  identical updated valuation. Each child stays in the `Family` type.
- For a selected coordinate truly in the union source support, every
  child family's union support is a subset of that source support with
  the selected name erased, strictly decreasing cardinality. A failed
  alternative can disappear; no equality of union supports is assumed.
- This does not construct a general high/recursive solver or claim raw
  typed-order Finsupp effectivity.
