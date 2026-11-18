# Executable highest nonzero profile piece: proposed implementation refinement

FiniteProfile supplies actual piece constancy and a literal finite cover, but its representative list is semantic, not executable. To avoid introducing an unchecked ordinal-code successor/partition compiler, implement the highest-piece decision by a proved finite norm-ball refinement.

For normal mu,nu,E set C=2+N(mu)+N(nu). Prove every exponent in the existing jointProfileRepresentatives has norm<=C and is below epsilon zero, by actual CNF weight inequalities and finite successor norm. In particular this covers 2, every actual prefix exponent, and its successor. No ordinal-norm monotonicity is used.

Use the already checked encodedNormalNormBall C, filter by actual code comparisons 2<=e<E and inequality rawProfileCode(mu,e) != rawProfileCode(nu,e), and fold with the checked raw ordinal comparison to select a largest remaining ordinal code. Return none if empty. All input codes are total; correctness only under normal input hypotheses. Prove this literal selector computable/primitive recursive, and:
- none iff the two actual profiles agree at every exponent on [2,E);
- some y implies y is in the domain, has unequal profiles, and for every unequal-profile x in the domain with y<x, x and y lie in the same exact joint piece;
- therefore selected y belongs to the highest nonzero piece, and its sign equals that at the source's chosen right endpoint, successor-top predecessor, or limit-top lower-edge+1 whenever those choices are made.

The finite norm ball refines the source finite breakpoint search; it is not the printed representative itself and makes no complexity claim. The proposed correctness condition pays that distinction explicitly by highest-piece identity and actual profile constancy. Its proof uses complete finite coverage: a different higher nonzero piece has a bounded representative strictly above y, contradicting the literal maximum.

This is supporting algorithm work, not prop:equal-gap. Global phase traversal, initial quadratic exceptions, terminal coefficients and the common effective tail are still unpaid. Request independent approval of this implementation refinement before concrete freeze; if exact source representative identity rather than piece-equivalence is required, implement the original breakpoint compiler instead.
