# Generic-control finite-coefficient identity

Foundations.tex lines 268–277 states the finite-coefficient identity psi(omega*k+n)=Phi^[k](2*k+n)+k. This component is a separate generic-control proof for the actual collapseWith G, not an assumed replacement of Phi by Gamma in that theorem. It is directly relevant to the finite-iteration wording of paper09 hardness.tex lines 316–319.

Hypotheses are explicit StrictMono G and identity majorization n≤G n. FiniteBoundary includes coefficient zero. For coefficient a+1, maximizer is exactly (a,G(2*(a+1)+b)-2*a); ExactMaximizer proves its actual predecessor membership, exact norm budget, attainment of the proposed formula and domination of every actual finite-pair predecessor. Natural subtraction is justified by the majorization premise, not treated as integer subtraction without a bound.

ExactFiniteCoefficient identifies the actual value on omega*a+b with (G^[a])(2*a+b)+a, using the actual predecessor maximum equation. The iteration count a is input-dependent. This is a value identity, not a bound on the existing worklist's step count or execution cost.

Primitive-recursive evaluation, coded syntax folds, fixed-Gamma specialization, compositional whole-source bounds and changes to the earlier fixed-iteration qualification remain separate. No input-independent iteration count, global ordinal monotonicity, manuscript/register/export change is asserted.
