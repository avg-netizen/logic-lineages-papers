# Exact original counter comparison

Source08 paper.tex lines 458–469: counters on an effective tail are compared by their actual leaders; ties are compared by rank, and equal ranks with equal leaders give equal whole values. The actual kernels, leaders and original inputs are unchanged.

The explicit sufficient pair-dependent threshold is max(CounterLeaderBounds.threshold n c, CubicLeaderRecognition.leaderTail n c e), used separately on each original input with masses swapped for the second. This combines precisely the saved half/three-quarter and actual cubic recognition tails. It is not claimed minimal and is not a global uniqueness claim outside those tails.

The strict target is the literal lexicographic alternative H1<H2 or (H1=H2 and n<m). The equality target gives actual leader-and-rank equality, then equality of all three original parameters n,c,t using same-rank recognition. The equal-leader larger-rank case must use the already proved actual collision, not an assumed rank-order rule; the unequal-leader case uses the proved actual exponential gap.

Quantitative divergence of collision residuals and arbitrary fixed outer shifts remain separate. No whole lem:counter, lem:uniform or arithmetic decision promotion is asserted. No accepted files, numerical semantics or resource caps change.
