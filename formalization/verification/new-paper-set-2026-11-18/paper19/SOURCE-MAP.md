# Current19 perturbed-control full lemma scope

Source: 19-source-expressivity-and-control-sensitivity/sections/control-sensitivity.tex,
`lem:perturbed-control`, imported unchanged from17377d6d.

Reused definitions: `fastControl 0 n = 2^n`, successive level = input+1
iterations; `Phi n = fastControl 5 (n+100)` is source G.
`PerturbedControl.error b H n` is zero at0 and on[0,b], otherwise the Boolean
bounded simulation H at (valuationTwo n,n). `control = Phi + error` is literal
Gamma_b. valuationTwo is the old actual bounded divisibility-search definition.

Target includes primitive recursion, preserved finite prefix, nonnegative
natural difference≤1, Phi≤control<Phi(next), the NEW double-exponential
successor lower bound, additive margin at every a≥1, eventualF6 bound (explicit
N=101), and literal real epsilon-N ratio limit1. No new control definition,
range restriction, control-growth premise or halting oracle is introduced.
Quantifying over every primitive-recursive Boolean H is stronger than the
single fixed simulation H in the printed lemma, and does not assert hardness.
The old full target lacks the double-exponential clause and is not itself
sufficient for this new target.

Proposed supplier: existing exact `Phi_succ_gap n` proves
2^(2^(Phi n+1))≤Phi(n+1). Since control n≤Phi n+1 and
Phi(n+1)≤control(n+1), two applications of monotonicity of natural exponentiation
supply the new bound. Every other printed clause has an existing actual-control
proof, whose exact dependency chain must be checked before acceptance.
No global ground hardness or paper19 completeness claim.
