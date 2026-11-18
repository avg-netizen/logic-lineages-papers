# Actual Spine.Expr marking and concrete free-substitution typing

New definitions operate on the checked locally nameless Spine.Expr directly.
No theorem about the earlier named carrier is imported as if it applied here.
mark traverses original initial lambdas, blocks both free and bound variable
heads, changes an ordinary head into its literal marked owner with empty
extras, and fixes an already-marked owner exactly. headmark is total and
retains failed variable spines. Source is ordering.tex persistent partial
marking definition and successful marking covariance in structural stability.

Freeze eight exact endpoints: successful persistence, headmark idempotence,
success/headmark agreement, partial and total typing preservation, successful
mark/freeSub covariance, concrete freeSub typing under a binder prefix, and
its empty-prefix endpoint. Do not claim headmark covariance or failed-mark
covariance: substituting a free variable can expose a head.

Typing transport uses actual typed images in outside Γ, possibly with outer
bound indices. Derive shifting into a retained List Ty prefix by context lookup
induction, then use the previously checked shift typing theorem. Prove mutual
term/base/extras typing preservation under that literal prefix, increasing both
prefix and insertion depth under lambdas. The final endpoints do not assume
lifted image compatibility or result validity. This closes a real transport
obligation rather than merely outer annotation preservation.

All source maps and prior semantic definitions stay pinned. This packet does
not claim alpha/name correspondence, comparison closure, or any complete
numbered manuscript theorem. Literal comparison/occurrence witnesses follow.
