# Effective sufficient original occurrence budget for the exact charge

[Paper 17 arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex)
164–195 defines the finite structural charge, including ordinary support
and rank powers on grouped count support. Lines 225–233 use the initial
charge as an upper bound on actual branch depth.

Map each chosen ordinary support key and each count support key
back to its literal original LowerOperand using the existing
injective embeddings. Their images are disjoint (ordinary and
count constructors), and both are contained in the exact signed
grouped support. The grouped support maps back to some original
raw occurrence for each key, so its distinct cardinality is at most
the original occurrence length. Canceled keys can only disappear;
there is no assertion of positive coefficients, uniqueness of raw
occurrences, or equality between support and raw length.

Every count support key has a genuine Fin r rank, so its weight
is at most 3^r, and each ordinary occurrence has weight one.
This yields the sufficient occurrence length times 3^r bound on
both actual state charge and exact syntax charge. If r=0 the two
ranked supports are empty and exact charge is zero. The budget is
not asserted to equal exact charge.

The raw syntax program computes only length times 3^r and is
primitive recursive by list length and natural power recursion.
On canonical encoded weighted syntax it equals the same upper
budget. Totality on malformed codes conveys no validation or
actual field semantics. This is suitable as an independently
supplied sufficient alphabet expansion budget, not a proof of the
exact-charge global-tail code, actual tail payment, or a symbolic
branch compiler.
