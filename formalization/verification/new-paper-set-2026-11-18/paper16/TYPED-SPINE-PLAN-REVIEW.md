# Independent typed-spine plan review

Approved to define and freeze concrete typing/endpoint targets before proofs.
This is plan approval only, not approval of unseen Lean declarations.

The plan correctly retains existing actual Expr/Args and shift/substitute/
applyAux rather than replacing them by a typed evaluator. Free variables carry
their source type/name pair, while bound context lookup determines index types.
Head bases must still respect original declarations; arbitrary marked output
annotations and individually typed extras match the auxiliary syntax.

The proposed final parallel-substitution premise is a concrete finite list of
values typed in the outer context and a source typed under the prepended type
list. No abstract success/preservation supplier is left in that endpoint.
Nearest-first list order matches applyAux's reverse accumulation of consumed
original lambdas. Variable-image compatibility is an acceptable structural
helper only if discharged internally from this list, including external
indices and lifting under remaining binders.

The proposed call endpoint correctly requires source typing, a typed argument
spine for the original arrow type, and actual successful apply. It must not
assume result validity or substitute before deciding an original residual
variable branch. Derive annotation agreement and consumeTypes success from
actual typing/spine rather than a supplied oracle. Preserve the original
context for all external arguments and simultaneous inserted values.

This will establish typing for this locally nameless auxiliary presentation,
not alpha correspondence with the earlier named carrier, general successful
application covariance, or full comparison preservation. Exact statements
and hashes require another pre-scope pass when available. No compilation here.
