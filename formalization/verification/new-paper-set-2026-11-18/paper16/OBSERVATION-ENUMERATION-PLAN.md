# Actual ports and target observation enumeration

Next bounded exact scope, after the reviewed inventory packet. No native work or target definitions have begun for this plan.

## Port contexts

Use exactly B positions, represented by a List (Option Ty) of length B. A used slot stores its type; extensions preserve every existing Some entry and may fill None entries. Enumerate contexts by a B-fold finite product of None and Some of types in the actual K list. Prove membership iff length B and every used type in K; retain actual coordinate indices, not permutations or cardinality-only witnesses. Count used slots by a recursive count. Prove extension reflexivity/transitivity, used-count monotonicity, and existence of an unused index whenever used < B.

Port i has natural name freshBase+i, where freshBase is one plus the maximum numeric component of the actual finite V inventory (zero-based maximum for empty V is harmless). Prove disjointness from V and pairwise distinctness of numeric port names. Typed port variables use the type stored at their slot. Existing assignments are preserved literally by extension.

## Target occurrences and external binder assignment

Enumerate actual raw target subterm occurrences, preserving repeated occurrences and a nearest-binder-first type stack. Descending through a lambda prepends its domain to the stack; descending into every ordered base/extra position retains the stack. The initial target is ordinary, but total raw enumeration can retain marked extras without granting a marked-target result. An occurrence carries its original raw term and binder stack, not just an equality-deduplicated set.

A concrete finite assignment chooses, for EACH enclosing binder, a used port of the same type. Enumerate these choices by recursive products of the actual used coordinate list. This allows reuse of a port where the printed observation definition permits an arbitrary appropriately typed assignment; canonical fresh-opening paths will use distinct slots and form a proved special case, not silently narrow the observation family.

Open the occurrence by the already checked simultaneous bound substitution with its nearest-first tuple of free typed port variables at depth zero. Prove that an original typed target yields occurrence typing in the literal binder-stack context, that the assignment tuple is typed in EmptyContext, and that the opened occurrence is typed in EmptyContext. Prove total full external-bound-slot replacement from scoped typing, without identifying this operation with full application.

Filter the resulting finite candidates by their annotation/type and the printed residual depth budget: raw occurrence lambdaDepth <= B-used(context). Prove enumeration soundness and completeness against this literal occurrence/assignment specification, including multiplicities and functional-result observations. Use computable membership/filter booleans with proved equality tests, not Classical.choose or a mere Finite instance.

## Remaining normalization obligation

A target lambda observation consumes one unused port; its opened body must be shown to occur in the extended observation family with the actual binder-stack assignment and updated residual budget. Literal target bound occurrences, simultaneous substitution composition and preserved old port indices are paid internally. Then normalize arbitrary fresh names in actual comparison derivations to these available canonical ports via the accepted injective equivariance/fresh-opening synchronization. This latter joint original comparison/list derivation bridge and recursive source inventory closure are separate exact freezes; finite enumeration alone is not lem:observation-closure.

No finite-domain lattice, original-spine tuple table, fixed point, decision adequacy or well-foundedness conclusion is claimed by these packets.
