# Round2: actual shifted hyperfunction collision window

Primary Snyatkov2008p42Lemma4, checked directly on rendered original PDF; primary
URL/hash in SnyatkovInverse-SOURCE.md. Source terms are EXACTLY
Phi(H(u)+e), Phi(H(v)+k), with the original fixed-seed H and signed e,k. The
compiled numeric terms totalize negative arguments with toNat, but the gate
pays that the original signed arguments are nonnegative above the explicit
bound c+|e|+|k|+1. No change to the original variable-seed Phi control.

Use accepted actual inverse roundtrips/monotonicity/compression to eliminate
Phi a<=c*Phi b into a<=b+c. Then H(u)>=H(v+1)=Phi(H(v))>=2H(v), while H(v)>v.
For v at the displayed bound, the source signed inequality is impossible.
The window is on the smaller index v ONLY; the larger u is not asserted to be
bounded by c,e,k. This pays a concrete finite-exception dependency of source
quantifier elimination, not the full arithmetic solver or a source-label
promotion. All-code primitive recursion is required, not merely an existence
of a finite bound. Comparator must compile/freeze before candidate proof.
