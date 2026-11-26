# Independent free-substitution covariance plan review

Approved to define and freeze exact algebra and covariance targets before
proofs. This reviews the proposed equations, not unseen Lean declarations.

All three algebra equations have the necessary depths and block lengths.
For insertion cancellation, shifted indices at/above c land beyond the whole
removed block; indices below c are protected. Under a retained lambda both
cutoff and substitution depth increase together. This is not a closed-image
special case. For freeSub/shift interaction, inserting a free image after the
outer shift requires lifting it by k+d, matching shift at cutoff d of an image
already lifted by d. Lambda traversal again increments the inner cutoff/depth.

In simultaneous composition, the original q receives free images at
(d+values.length), whereas external replacement values receive freeSub at zero.
For a replaced bound index, interaction moves freeSub through shift d; for a
free occurrence, insertion cancellation removes the extra block lift. Retained
and beyond-block bound indices are unchanged/decremented respectively. Mutual
Args equations and old base/extras traversal are essential, not optional.

The suggested raw annotation helper is legitimate: if every θ σ x has outer
annotation σ, shift preserves that annotation, so freeSub preserves every raw
outer annotation structurally. Actual applyAux branches require annotation
checks only, not a typing derivation. Such a stronger raw helper may simplify
proofs provided the final typed endpoint derives the annotation condition from
actual typed images and retains the promised source/spine premises. It must
not use a supplied call-covariance or output-validity condition.

Success-only is essential. An original free residual can fail before θ but
become an applicable head afterward, so unconditional Option.map equality for
failure is false and excluded. A successful call cannot encounter that branch;
original head/binder branching and one-shot append must remain unchanged.
Images are allowed outer bound indices and are not recursively substituted.
No alpha bridge or ordering stability is established by this plan. Freeze and
independently review exact new definitions/targets before proof authoring.
