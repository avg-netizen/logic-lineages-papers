# Independent pre-scope review: current19 perturbed control

Approved for candidate/native preflight of complete lem:perturbed-control.
Independently rehashed all three Lean pins and the current manuscript pin;
all match. Read the full lemma and its preceding bounded-simulation definition,
actual SourcePerturbedControlDefinitions, literal hierarchy and expanded target.

Every printed clause is represented: primitive recursion, equality on [0,b],
distance in [0,1], G majorization and strict next-G bound, full double
exponential successor growth, additive margin for every a>=1, eventual F6
bound and the real ratio limit one. Threshold101 is explicitly justified in
the source proof and is stronger than the bare eventual statement. Natural
subtraction in the distance clause is harmless only together with the
separate G<=control conjunct and actual definition control=Phi+error; both
are present. RatioLimit is the actual real epsilon-N absolute-error limit,
not a surrogate estimate or qualitative placeholder.

The unchanged Phi is precisely F5(n+100), with F0(n)=2^n and Fj+1 defined by
n+1 iterations. The actual error is zero at zero and on the finite prefix;
otherwise it is the Boolean value H(valuationTwo n,n). valuationTwo uses a
literal bounded divisibility search, not an oracle. Its existing supporting
proof characterizes the exponent at positive n; native reconciliation of
that implementation and all other suppliers is still required.

The source fixes one primitive-recursive bounded simulation H before all
queries. Universal quantification over fixed primitive-recursive Boolean H
is a legitimate strengthening of THIS growth lemma: specialization yields
its control estimates, and the only assumed property is the exact primitive
recursiveness already stipulated in the source. No simulation correctness,
diagonal nonhalting, nonperiodicity or hardness conclusion is asserted by
the target, so no halting oracle is hidden in this generalization. The
concrete simulator/halting correspondence remains a separate obligation
for the later ground-hardness theorem; this target cannot discharge it.

The old fourfold-growth result is insufficient by itself. The new literal
2^(2^control(n)) bound must be proved, and the proposed actual Phi_succ_gap
plus Phi<=control<=Phi+1 route matches the source argument. No growth
hypothesis or alternative control has been added to the proposition.

No native acceptance or numbered promotion yet. Require exact alias,
standard-only axiom closure and full recursive source/artifact/receipt
reconciliation followed by independent final review. No compiler invocation
or Lean/source edit occurred in this pre-scope review.
