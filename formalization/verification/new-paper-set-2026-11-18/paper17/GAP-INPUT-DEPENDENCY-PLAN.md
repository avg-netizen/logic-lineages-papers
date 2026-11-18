# Next dependency plan toward full gap/input comparison

Planning only; no frozen target, theorem or acceptance.

After full one-step propagation, prove its printed event-count-lag consequences
on actual selected-control relative entry trajectories. Strict dominance at lag k
must survive until the lower last event and force upper count≥lower count+k+1;
weak dominance yields ≥lower count+k. Boundary indices at stopping require actual
first-finite equivalence, not an assumed count/order oracle. Upper still-running
status must be proved at each induction step before invoking its recursion.

For source lem:gap-input(i), initial relative limit parts are actual gaps delta_P,
delta_Q. With strict gap and same t, choose effective tail at least S and all
source norms; selected control grows by at least S on this tail. Strict one-step
propagation plus lag consequence gives strict counts, then strictly expansive
iterate yields strict terminal norm. Use full actual endpoint orbit.

For (ii), need a separately proved adjacent-control additive margin
f(u+1)≥f(u)+S on effective tail (derive from frozen double-tower growth, not merely
StrictMono). Then t>u preserves S slack at every next pair of orbits; generalized
weak gap propagation handles either initial strict or equal gaps. Strict terminal
value uses unequal starting input and the count inequality.

For (iii), preserve k successive actual reserves delta_Q+omega*(k-j) before
applying weak lag k. Candidate norm estimate N(delta_Q+omega*r)≤N(delta_Q)+2r
must follow full RelativeNorm/finite coefficient norm, not ordinal norm monotonicity.
N(delta_Q)≤N(lambda_Q) follows mu_Q+delta_Q=lambda_Q and RelativeNorm.
Tail enlarged by2k pays reserves; positive S=max(1,NmuP,NmuQ) and u+S≤f^k(t)
provide the terminal strictness including zero-target edge case cited in source.

All three clauses must retain effective (preferably explicit) tails and actual
chosen controls. A purely eventual existential with no effective production is
not enough for source arithmetic. Full numbered promotion waits entire packet.

## Candidate explicit tail after preliminary inequality inspection

A plausible uniform base tail is 2+N(lambdaP)+N(lambdaQ)+S, with +2k for
clause(iii), S=max(1,NmuP,NmuQ). This is deliberately stronger than the printed
max lower bound and remains a proof obligation, not an accepted estimate.
Selected f(v)≥G(v)≥2v+4 supplies same-input slack once v≥S. Exact adjacent
double-tower growth supplies f(v+1)≥f(v)+S whenever v≥S. Strict monotonicity of
iterates then supplies each unequal-orbit next-budget margin, but is NOT used
alone to infer the additive S margin.

For lag-k reserves, N(deltaQ)≤N(lambdaQ) follows relative norm; ordinary-addition
bound gives N(deltaQ+omega*r)≤N(deltaQ)+2r. Proposed tail pays this plus NmuP.
The positive deltaQ forces upper process to remain running through lag k.
At lag k, f^k(t)≥u+S>u supplies strict initial numerical input for the eventual
terminal inequality. Full proof must establish these details at actual indices.
