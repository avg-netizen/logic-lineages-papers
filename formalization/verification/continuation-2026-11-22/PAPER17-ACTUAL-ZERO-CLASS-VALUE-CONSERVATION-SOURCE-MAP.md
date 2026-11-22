# Signed value conservation for the very same actual zero-class witness

[Paper 17 arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex)
130–162 gives the original signed zero-class replacement, including
ended, same-input and higher transfers; 215–224 requires that the
canceled errors are replaced exactly, not dropped before the next class.

The actual aligned annotations give the doubled signed coefficient
decomposition without any maximization or cutoff assumption. The upper
class choice in the manuscript is needed for the separate logarithmic
bound and sign branch, not for the exact identity. The zero test here
is the original `rowParts.1 = 0`, not a new signed condition. Original
short-prefix affordability (`Ready`) remains explicit. Existing
`exactRetainedRemainder` installs all signed corrections and the exact
short/identity counts. Existing `exactResidualPartition` preserves
the actual outside read list and splits its signed sum from the cohort.

The exact `moved` argument is related by the original `MovedAt` at the
original least prefix and must already have lifted actual reads. This
is precisely the witness returned by #895/#896; this theorem never
constructs or chooses a second witness. Induction on its actual
`MovedPrefixes` constructors preserves the value of that exact list.
Same-rank counts agree. For each true higher transfer, the certified
count equation gives signed p=q+i and the literal emitted source
weight times q equals the same signed weight times p minus weight
times i. No nonnegativity of signed weights, independent field
valuation, or arbitrary H domain is assumed. The no-survivor case is
literally the empty cohort and moved list.

The resulting live original read packet is exactly
`outsideCohort … ++ moved` at the unchanged raw assignment, with
constant exactly the original value plus the `replaceRow` shift.
Its ranked representation is literally the same `concreteRow` of
#895/#896, and the whole original raw signed value is recovered
through exact successful normalization at that same assignment.
This is a local semantic transport, not an arbitrary replay,
short-successor cleanup, proof of next-node rank/guard closure, or
a normalization loop/effectivity/numbered promotion.
