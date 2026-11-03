# Actual unequal-leader counter order

Source08 paper.tex lines 466–468 and 490–493: distinct leaders are distinct values of the literal control f, their exponential gap separates the actual counters using the strict half/three-quarter bounds.

The first target proves the printed gap 2^(H1+1) ≤ H2 for all actual leaders H1 < H2, without a domain restriction. The existing strict monotonicity and stronger successor gap of Phi imply this directly from the actual leader preimages.

The second target retains exactly CounterLeaderBounds.threshold on each original input, namely max(c+2r+1,2c+10) for r=n+3 and separately for the other rank/mass. These are explicit sufficient tails, not asserted minimal. Both actual counters retain their original ranks, masses and inputs. No equal-mass or cubic recognition premise is needed. Unequal leaders imply the exact strict-order equivalence and unequal actual counts.

Equal-leader rank ordering is handled by the previous component. This component does not claim divergence of collision residuals, arbitrary outer fixed shifts, whole uniform separation or whole lem:counter promotion. No new evaluator, basis, oracle or accepted-source modification is introduced.
