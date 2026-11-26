# Finite typed alphabet for actual zero edges and traces

[Paper 17 arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex)
130–162 supplies the exact surviving-prefix and higher-to-least-rank
transfer syntax; 225–233 calls for finitely many resulting labels.
This packet bounds labels only, not a symbolic branch compiler.

An alphabet is a finite list of the original typed LowerOperand keys.
From each count key (rank, λ, μ) extract (rank, λ, prefixTarget μ).
The expansion keeps the alphabet itself and appends the prefix count
operands, plus one candidate canonical H for every strictly ordered
prefix pair. P is the candidate higher source, Q the candidate lower
anchor; the H key is exactly replacementOperand Q.rank P.λ P.η Q.λ Q.η.
It uses Q's original rank and λ and adds the original P gap to Q's
prefix target. No weight, numerical read, valuation, selected class or
collision guard is consulted. Some generated candidates may be
impossible or invalid; membership itself asserts no hit or properness.

For an actual ZeroEdge, original successful read normalization gives
actual source liftedness and original normalized-key provenance.
#883's exact outside complement proves each kept outside key was
original. #899's cohort provenance gives a prefix label from the
source-only list for each original survivor, including the actual
least anchor. The actual MovedPrefixes derivation emits the anchor
key, or additionally the exact H for its strictly higher source.
The installed actual short cleanup only takes a subsequence, so the
exact cleaned state uses only these operands. No anchor means no moves.

Iterating that expansion once per actual edge covers a given Trace's
endpoint operands; its true edge count plus remaining charge is at
most the starting charge. The expansion does not enumerate semantic
branches. No uniform numeric tail, future actual label oracle,
sign/weight bound, code effectivity, all-tree branch enumeration or
dimension induction is claimed.
