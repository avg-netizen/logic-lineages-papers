# General typed parallel substitution and original-spine calls

Use the already frozen locally nameless Expr/Args, not a renamed version of
old Paper06 and not the previous named syntax. Bound contexts are functions
Nat -> Option Ty with explicit push; free names are pairs (Ty,Nat), as allowed
by the paper's typed-variable convention. Head bases check their unchanged
original declarations; marked outputs may be retyped and extras are typed
individually. No alpha-quotient of the earlier named carrier is claimed.

Auxiliary structural lemmas may assume lookup compatibility only at variables:
actual shift transports a typed tree along the index shift; actual substitution
transports it when every substituted bound-variable image is typed. Binder
lifting of this premise is proved using the checked BoundUnderBinder equation,
not supplied by the caller. These are helpers, not the final endpoint.

The endpoint uses an ordinary typed finite value list. If values has types
[σ0,...,σn] in Γ, and q has type τ under that list prepended to Γ, then
substitute values 0 q has type τ in Γ. Derive the variable compatibility
internally by induction on the typed value list: index0 inserts the first
value; successor indices reduce to the tail; the empty list is identity.
The environment order is nearest removed binder first. No caller-supplied
result validity is allowed.

Define a typed argument spine by the original arrow decomposition: each
argument is typed in the outside Γ and consumes exactly one domain. Prove
that consumeTypes returns the final τ from this spine. For the actual
applyAux, maintain q typed under the accumulated value-type prefix and
values typed in outer Γ. A lambda consumes the next original binder and
pushes the supplied argument; exhaustion invokes the concrete substitution
theorem. An original variable cannot yield a successful nonempty call.
An original ordinary/marked head invokes typed base/extra substitution,
appends the original typed arguments once, and uses the computed suffix τ.
Finally apply's empty branch preserves q, and its nonempty branch uses an
empty accumulated environment.

All proofs use existing actual functions. The final successful-call theorem
has only original source typing, typed argument spine, and actual success
as premises; it concludes output typing. No comparison relation, full
substitution covariance, alpha bridge, or numbered theorem is thereby proved.
