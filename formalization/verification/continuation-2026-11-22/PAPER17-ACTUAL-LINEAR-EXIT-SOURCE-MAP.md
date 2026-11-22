# Original correlated linear exit at the greatest raw rank

[Paper 17 arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex)
173–176 and 197–205: after zero coefficients are removed, if there
is no nonlinear occurrence at the greatest coordinate z, retain the
entire row as a linear row in z with correlated lower-input fields.

The original read list is lifted and bounded by the declared greatest
raw rank. Its exact successful original normalization is supplied.
Actual normalization guarantees the retained weights are nonzero,
each operand came from the original raw list, and the signed sum
agrees at the original valuation. Absence of an active nonlinear
occurrence at greatest rank makes every normalized occurrence there
either its coordinate or its zero iterate; no positive iterate, entry
or count is relabeled linear by this packet.

Lower reads are the literal ordered filter at strictly smaller raw
ranks, retaining every signed weight, operand, and actual value.
The prepared row keeps its original constant, one signed slope on
name zero (the greatest rank), then each lower occurrence's original
weight at name j+1 in its unchanged table order. No lower field is
evaluated into the constant. The produced order atom has the existing
`PreparedInput` shape. A canonical table valuation exists, and every
actual tied valuation is forced by the original exact per-slot reads,
all at the same original raw assignment. Lower ranks can repeat.

After any update of the greatest coordinate, the same table and
positive names retain exact ties. Replaying the live normalized list
changes only the actual linear values at that rank, in original order;
the prepared row at the updated assignment has exactly that signed
value. At the original greatest value this agrees with the raw row.
No assertion is made that canceled raw nonlinear occurrences are
defined or replay at arbitrary new greatest values. Original branch
domain/pattern guards are not erased or proved here. No elimination,
automatic normalization, finite iteration, or effectivity claim.
