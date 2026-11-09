# Exact scaled-Phi interval and residue projection

Toward the dominant-case terminal of Snyatkov 2008 pp44–45, this packet fixes the concrete predicate domain(x+e) AND lower<=a*Phi(x+e)<=upper AND x mod m=residue mod m for positive a,m. Lower, upper and residue are arbitrary expanded terms omitting only the eliminated original name, under one retained valuation. No whole BASE/QE/normal-form statement follows from this restricted one-head clause.

The original signed domain begins at (-e).toNat, whose Phi argument is e.toNat. If the lower bound already holds there, that is the least allowed x. Otherwise the original floor inverse yields the true positive crossing and the least allowed x is (crossing-e).toNat. A finite compiler then tests exactly m successive values from this least lower witness, preserving EVERY original guard. Any satisfying original witness n reduces to x0+((n-x0)%m), retaining its original residue class and its lower bound while decreasing its Phi value, and hence retaining its upper bound.

The fixed literal natural remainder is t-m*(t/m), using the existing expanded signature. The two initial/inverse branches are explicit formulas; there is no semantic decision field, opaque runtime callback, supplied periodicity assumption or maximal-parameter restriction. Code output is total on all numerical inputs; source correctness and domain assertions require positive coefficient/modulus as printed in the exact targets.

The six propositions and exact definitions were frozen before any candidate proof. The earlier dominant-boundary proof packet remains a candidate awaiting its own exact gate; it is not yet an accepted dependency. No target-only preflight or proof has run for this packet.
