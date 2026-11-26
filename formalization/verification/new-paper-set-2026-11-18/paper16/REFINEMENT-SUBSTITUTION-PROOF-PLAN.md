# Actual two-environment free substitution proof route

Target remains the already-frozen RefinementSyntaxTargets.FreeSubstitution:
typed maps γ,δ in EmptyContext, pointwise actual refinement, and actual input
refinement imply refinement between actual freeSub γ 0 q / freeSub δ 0 s.
No additional validity, fresh-image, covariance or compatibility premise.

Use strong induction on the actual right refinement tree count, generalized
over both maps. For each lambda choose a typed name absent in both literal
bodies and in the finitely many relevant γ/δ images occurring at free leaves.
Compute a maximum over those actual image terms; never require a name absent
from the infinitely many images of the maps. Synchronize the original opened
witness to that name without changing count, then mask the maps at that one
typed name to the identity free variable. Pointwise refinement and typing of
the masked maps follow internally (var at the masked name, originals elsewhere).

Apply the smaller-tree hypothesis to the synchronized opened witness and the
masked maps. Existing full FreeCompositionProof.composition identifies this
result with opening of the transformed bodies at depth one. Masked and original
maps agree on the bodies because the chosen name was absent from the original
free leaves. No naive unshifted insertion is used: actual depth-one freeSub
remains, exactly as in freeSub of the outer abstraction. Thus no unproved
closed-image shift-identity premise is needed.

Freshness of the transformed bodies follows from the finite relevant-image
bound and the fact that actual shift does not change free occurrences. Typing
comes from the concrete freeSub typing theorem. Validity of every image follows
from its pointwise refinement tree, then shift/freeSub validity is structural.

All positional base witnesses and existing/whole-owner extras are mapped under
the same maps. For owner witnesses, actual annotation preservation derives
that the mapped target has its old type, aligning the mapped whole-owner root.
Arbitrary typed-name renaming is then the specialization to free-variable maps,
with pointwise var witnesses and no injectivity restriction. Opening at any
fresh name is a direct consequence of the already-proved synchronization.
No E/cut, application associativity, or substitution oracle is assumed.
