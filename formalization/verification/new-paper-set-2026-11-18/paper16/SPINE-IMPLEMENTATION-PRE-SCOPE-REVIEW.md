# Independent original-spine implementation pre-scope review

Approved for native checking of the seven frozen supporting equations only.
Reviewed SpineSyntax, SpineTargets, SpineProof against current paper16
sections/ordering.tex definition def:application and its following obstruction.
All three SPINE-FROZEN.json hashes independently match. No compiler run here.

The algorithm chooses cases on the original residual Expr, not its substituted
image. Consumed original lambdas push external arguments in reverse order, so
index zero receives the last consumed binder. A remaining variable blocks;
a newly substituted functional head or lambda cannot be inspected. At an
original head, substitution reaches old bases and extras, while the entire
remaining external argument tuple is appended exactly once in original order.
An already marked output, rather than its original head result, controls the
remaining suffix. consumeTypes checks each remaining argument annotation.
Exhausting the tuple returns the simultaneously substituted original residual.
The empty public call returns the syntax literally.

shift protects indices below cutoff. substitute protects indices below depth,
looks up the removed block at i-depth, lifts inserted external values by depth,
and lowers indices beyond that block by its length. Recursive lambda traversal
increments depth. This is the expected locally nameless block substitution;
it does not sequentially substitute into earlier inserted values.

Targets faithfully state empty-call identity, free/bound variable blocking,
two concrete under-binder equations, and the printed obstruction specialized
to native successor and a ground free variable. Successor has the required
functional type; the identity function admits the complete two-element tuple.
The seven proof drafts are reflexivity equations, not general preservation
proofs. Their native validity remains to be checked by the authorized queue.

Scope limits: this is raw annotated syntax with no well-typedness premise or
binder-context validator. Type annotations used to reject mismatched calls do
not constitute a general typing theorem. The capture examples are not a proof
of full capture-avoiding substitution correspondence. No alpha equivalence,
fixed-signature correspondence, successful-call substitution covariance,
associativity, or numbered manuscript theorem is credited. PLAN describes a
future typing layer; it is not implemented by this packet. These explicit
limits are consistent with the frozen scope and must remain in final claims.
