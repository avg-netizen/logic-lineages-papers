# Genuine fraction-expansion bridge: proposed next scope

Avoid assuming canonical output regularity or importing the heavy old Laurent stack. Work with actual p,q : Polynomial K and q.coeff0 !=0, with genuine rational f=E(p)/E(q) and independently defined series expansion S(p,q)=(p:PowerSeries K)*(q:PowerSeries K)^(-1).

First prove rational square-root fraction update for BOTH digits from actual decomposition uniqueness, not a denominator oracle: rationalDigit b f = E(sqrtDigit b(p*q))/E(q). The corresponding actual C equality is the true branch.

Then prove the actual unrestricted-series operation gives seriesC(S(p,q))=S(sqrtDigit true(p*q),q). The proof uses polynomial square decomposition and the actual inverse of the unit series q; characterize the resulting square decomposition by the already proved series uniqueness. Nonzero constant coefficient proves q is a unit, paying every cancellation. Combining this equality with the unrestricted-series coefficient theorem yields every output coefficient sqrt(input coefficient 2n+1).

For representation independence, prove whenever E(p)/E(q)=E(p')/E(q') and both denominators have nonzero constant coefficient, S(p,q)=S(p',q'). Clear actual rational denominators, reflect equality through the polynomial embedding, then map that polynomial cross-product identity into PowerSeries and cancel the proved units. This makes the map an actual rational expansion, not a pair-specific unrelated output. The common-denominator update proves output regularity by its genuine representation; an explicit theorem about the canonical denominator can follow if needed but is not assumed.

This is a real regular-at-origin rational compatibility target. A rational pole at origin still needs Laurent/local-coordinate handling. Thus it does not silently finish full lem:local for arbitrary rational inputs unless the source coefficient clause is explicitly scoped to ordinary power-series expansions. Mixed pole/properness/transient obligations remain separate.

Imports would join the accepted Basic rational stack with accepted Series stack and PowerSeries.Inverse. Cap feasibility is untested; use only unchanged checker after frozen-target review. No existing accepted source changes.
