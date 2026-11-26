# Paper 17: executable nonempty exact dense chart enumeration on serialized signed-bit families

Printed source: `arithmetic.tex`, identification of equal raw coordinates
and choice of strict base order in `thm:arithmetic`.

- Use the already executable sorted duplicate-free actual source union
  of the original encoded rows, including every zero or cancelled
  occurrence. Enumerate the original finite assigned ranks at each
  width, retain the exact onto checks, and require nonempty width.
- For any duplicate-free source list, a dense assignment cannot assign
  conflicting ranks to the same name: the original entry-name tape
  equals the supplied duplicate-free source list. Prove exact density,
  nonempty width and literal consistency iff enumerated, not merely a
  one-direction feasibility claim. This does not assume consistency
  for arbitrary repeated-name lists.
- The existing exact lifted actual-pattern witness now lives in this
  executable enumeration at every valuation on a positive-dimensional
  literal family. Each retained name is inside the width and recovers
  its original value under the same genuine realized chart. Its width
  does not exceed actual union cardinality.
- Prove PR for the original finite choices, onto predicate, pattern
  list, width filter, and raw composition. No read or valuation is
  needed to generate candidate patterns. For a literal valuation only
  the true actual guard justifies rank recovery.
- No equality of list order with the earlier noncanonical
  `Finset.toList`, no numerical bounds or high-route logic, no
  compiler effectivity beyond chart enumeration, and no decision
  theorem or promotion.
