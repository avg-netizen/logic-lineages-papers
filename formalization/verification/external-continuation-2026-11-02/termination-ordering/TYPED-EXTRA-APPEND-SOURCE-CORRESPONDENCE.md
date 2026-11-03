# Whole-list typed extra append and restriction

Source paper06 marked full tuple append, lines256–260, and the exact downward-image append equation in lem:operator, lines307–314. This is a concrete prerequisite, not the entire operator lemma.

appendRaw takes the actual existing Extras downset and a list of actual K-typed Packed values. Each output fiber consists EXACTLY of its old members or values below some member of the entire supplied list in the already proved same-type PackedLE order. Native extra membership/availability is not replaced by a shape predicate. No supplied argument position is skipped; SuppliedIncluded explicitly retains every supplied member. Multiplicity and order are forgotten only in the downset representation prescribed by the source, not by replacing one full tuple table with a sequence of unary applications.

MembershipCalibration is a definitional interface. DownwardClosure and LeastClosure prove that this is the actual least downset containing old extras and all supplied values, not an arbitrary closed overapproximation. EmptyIdentity pays the zero-supplied-argument case and does not introduce bottom into an empty extra set.

AppendMonotone uses actual packed-order coverage of supplied values, not only literal list inclusion: every old supplied value must be below an actual newly supplied value of the same type. This supports genuine pointwise monotonicity of full typed tuples. The extra component is ordered by actual fiber subset.

RestrictionAppend is the exact source equation: downward image of the append equals append of the already down-image-restricted old extras with the COMPLETE mapped supplied list. It uses actual Value weakening, actual typed packed order, and the accepted downward-image map. No meet preservation of that map is assumed.

The append definition is ordinary executable finite filtering under decidable symbol equality. Its packed equality algorithm is derived from the already proved actual packed partial order, not classical choice. The candidate may assemble an ordinary Extras-valued append using the proved downward closure. No semantic realization/compression of source extras, structural interpretation, operator monotonicity or fixed-point theorem is inferred here.
