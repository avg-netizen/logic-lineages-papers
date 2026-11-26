# Signed absolute coefficient mass along actual normalized reads

[Paper 17 arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex)
130–162 gives actual same-rank and higher count replacements with signed
coefficients. Lines 197–233 require finite coefficient bounds for the
eventual sign cutoff; this is the weight-mass component only.

The mass of a read list is its literal sum of absolute integer
coefficients (not a sum of evaluated fields). Exact read
normalization retains one coefficient per original grouped key.
The finite Finsupp mass is subadditive: expand both sides to the
union of the signed supports, use the integer absolute triangle
inequality, and note that coefficients outside support contribute
zero. A singleton has exactly its weight's absolute value. The
exact normalized order of original grouped support and exact
coefficient records identify normalized mass with that Finsupp
mass. So successful actual grouping cannot increase it, including
signed cancellation and repeated raw keys.

Induction on the literal DisposedOrigins relation proves each
original count contributes at most two equal-magnitude coefficients:
ended emits none, same emits one original signed weight, higher
emits that weight and its negation. Actual outside reads are a
sublist by the original filter and actual origin input reads are a
sublist of the same normalized source via class selection. Thus the
same intermediate outside ++ moved list costs at most three times
the normalized source mass (coarse; no disjointness assumption on
these estimates). Literal short-count cleanup only filters it. The
actual final ZeroEdge mass is therefore at most three times its
original source mass, on the exact witness, without a new guard.

A trace with true edge count n yields final weight mass at most
3^n times initial mass. This packet supplies neither signed constant
growth nor bounds on recognized short-count offset factors or sign
cutoff. No computed cutoff, uniform compiler or arbitrary replay.
