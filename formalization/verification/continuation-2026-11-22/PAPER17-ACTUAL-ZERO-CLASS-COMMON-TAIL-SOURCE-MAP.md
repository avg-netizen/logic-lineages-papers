# Original count syntax supplies the two local rewrite guards on one tail

[Paper 17 arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex)
lines 130–162 moves actual selected proper prefixes to the least surviving
raw input, and explicitly requires the intermediate norm bounds and
comparison domains. Lines 197–234 distinguish selecting the actual largest
class at a node from choosing tails for the whole finite symbolic tree.

Extract `(rank, λ, prefixTarget μ)` from every original count operand,
without testing coefficient, annotation, class key, valuation, or output.
The common bound is the maximum of the exact original short-prefix
affordability bound and the exact original `safeTailCode` over every
ordered pair of these finitely many labels (P higher, Q lower in any
actual strict transfer). The latter retains both the inverse-table and
P-versus-Q encoded gap-input bounds, without claiming dominance.

The structural provenance clause is unconditional: every member of the
literal `cohort` has its exact rank, source λ and prefix endpoint η in the
source-only list. The guard clause assumes original aligned annotations
and the syntactic numerical common bound paid at each source count label's
original raw rank. The first maximum pays `PrefixTailReady` and hence
`Ready` with the original implications unchanged. The real least-prefix
membership and provenance identify both labels of each actual higher
pair. The same pair bound is paid at each corresponding rank; hence
`TransferReady`. The guards do not require maximality of C (nor zero
leading coefficient), so they also apply when C is the already available
actual maximum. The actual maximum is required separately by the row
value and sign arguments, not supplied here.

The LongField shape and original count annotation affordability in
`CountTailReady`, construction of actual aligned annotations, and the
numerical common-tail hypothesis itself are **not** supplied. This does
not generate all future labels, remove short successor counts, handle
smaller strips, or establish code/Primrec or uniform normalization.
