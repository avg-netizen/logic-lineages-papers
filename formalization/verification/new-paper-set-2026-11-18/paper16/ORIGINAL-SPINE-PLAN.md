# Proposed next component: full original-spine application

Status: scope proposal, before implementation or frozen Lean comparison.

The manuscript explicitly permits typed de Bruijn representations. Introduce
a distinct locally nameless auxiliary carrier with typed free variables
(type,name), typed bound indices, lambdas, native/binary/ranked ordinary heads,
and persistent marked heads with separate original base and ordered extras.
Typing uses a binder-type list plus the declared type attached to every free
name. This avoids capture-prone named substitution. The existing named raw
marking packet remains intact; it is not silently reinterpreted.

Implement ordinary lifting and simultaneous capture-avoiding substitution by
an explicit list of external arguments. Under a remaining lambda, increment
the depth and lift inserted arguments. Bound occurrences outside the substituted
block are lowered by the block length. Prove at least the zero/replacement/
under-binder equations and concrete capture-avoidance checks before relying on
this operation. Full type preservation requires a separate exact target and
must not be claimed from examples alone.

Full application walks the ORIGINAL initial lambda spine. Each consumed
argument is accumulated in reverse binder order; the residual syntax is not
substituted before the branch is chosen. If the tuple is exhausted, return the
simultaneously substituted residual. If entries remain and the original
residual is a variable, fail even when its eventual replacement is functional.
If entries remain at an original ordinary/marked head, substitute its old base
and extras, retain the original declaration, mark if necessary and append all
remaining arguments once. Determine the output annotation by consuming the
original residual arrow suffix and checking the supplied argument types.

The exact manuscript counterexample has θ=o→o, a functional free head h:θ,
and y:o. Here h must be an actual ordinary functional HEAD (e.g. native S),
not a variable, so staged application is permitted. The full call at λx:θ.x
with [h,y] fails because the original residual is bound variable0; the first
unary call returns h; the second returns h* with extra[y].

Do not claim unrestricted associativity, alpha quotient correspondence,
substitution covariance of successful full calls, comparator soundness, or any
numbered theorem merely from the implementation and counterexample. Freeze
exact support targets and independently review source alignment before proof.
