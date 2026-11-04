# The first-order invariants still required by paper06 lem:id1

This is a proof specification, not an accepted derivation. The current whole
target is `ContextUniformTargets.ActualContextUniformInternalAccessibility`.
R001 gives the actual finite ID1 proof judgment; the following source
invariants have not been discharged by semantic least-set theorems.

Fix n, arity, the finite subtype-closed S, its source heads and strict total
ranked precedence. Close their shared window code to a numeral c. The ONE
operator has I at even object codes and J at odd object codes. An object is
(Gamma, original canonical term code), or (Gamma, original encoded list) on
the J side. Gamma varies inside this same operator.

## Computability keeps the argument in the same ambient context

Let g encode Gamma and v be the original canonical term number. Write
`Obj(g,v,z)` for the fixed arithmetic graph of the actual product encoding,
`T_tau(c,g,v)` for the original typed carrier, and
`App_sigma_tau(c,g,f,u,z)` for canonical auxiliary application in that SAME
Gamma. The finite type recursion must define actual arithmetic formulas:

```
C_ground(g,v) := T_ground(c,g,v) and
                 exists z (Obj(g,v,z) and I(even(z)))

C_(sigma -> tau)(g,f) := T_(sigma -> tau)(c,g,f) and
  forall u (C_sigma(g,u) ->
    exists z (App_sigma_tau(c,g,f,u,z) and C_tau(g,z)))
```

The explicit g parameter is necessary. Quantifying arbitrary globally
computable object codes at an arrow, without restricting their ambient
context, would demand applications between unrelated Gamma fibers.
At a lambda, the body uses the arithmetic context-extension graph
`Extend(g,sigma,g')`; its base predicate is STILL the same I, at Obj(g',body).
No separate least set or additional inductive predicate is installed.

There are only finitely many tau in S. Any quantification over a type-tagged
computable value is the finite disjunction
`type = code(tau) and C_tau(g,v)`. This admits arbitrary type levels already
present in S. It is not a satisfaction predicate for all simple types.

## Accessibility and lambda induction

The type induction needs actual derivations of neutral/direct-reduct closure,
variables and bottoms, downward closure under original H and positive R,
and C_tau(g,v) implying I(even(Obj(g,v))). The accepted standard-N
computability lemmas do not supply these derivations.

Every I-induction invariant must bind the current object number and quantify
the retained context/value parameters with an Obj guard. For inverse
application, retain the literal application graph and all original R
descendants; do not replace the relation by reflexive closure. A bottom
argument is also available in the accepted semantic proof and may avoid a
fresh-variable transport obligation, provided the internal proof establishes
the exact same closure facts.

The lambda invariant retains BOTH body accessibility and the first-order
universal computable-instance premise. Quantify g, the body code and all
computable u in Gamma; use Extend for the body context and the actual
capture-free substitution graph for the beta instance. Function-side body
reduction, beta and bottom are the auxiliary-application cases. No
argument-side monotonicity may be inserted.

## Multiset and constructor induction

J induction binds an object (g, encoded multiset). Union induction retains
the other multiset and context parameters universally. Removed occurrence
origins and domination witnesses are finite arithmetic certificate data.
The singleton I induction retains all finite descendant lists and then
uses the union result. The source Direct relation is unchanged.

For constructors, code bases/extras as finite typed lists. `AllC(g,L)` is an
arithmetic formula using the finite type disjunction above. The invariant
for the outer base J induction universally retains later finite labels,
extra lists, result annotations, term numbers and g, guarded by the exact
constructor graph. Inside it use ordinary Nat induction on the finite label
and J induction on extras. The ordinary/unmarked omega case follows the
finite-label cases; no numerical Nat value is assigned to omega. The finite
external head-class induction retains the lower-head hypotheses. All label,
type/window, marking, Select, Copy, Mul, abstraction, argument and bottom
cases must be actual derivations in this same operator.

## The full substitution/fundamental invariant is uniform in context codes

The final structural invariant quantifies codes g,d,theta,q for source
context, target context, substitution environment and term. It says:

```
WT_S(g,q) and GoodSubstitution(g,d,theta) and ImagesComputable(d,theta)
  -> C_type(q)(d, Substitute(q,theta)).
```

The type-dependent conclusion abbreviates the finite disjunction over S.
`ImagesComputable` must be ONE arithmetic formula on an encoded finite
environment: quantify an index below the decoded length of Gamma, read its
type/image graphs, and require its C clause when that variable's type is in
S. Unused ambient declarations outside S must not make the invariant false.
This guard already agrees with the accepted `GoodSubstitution`, which asks
for a good image only under K(tau). Use that paid scope rather than adding
an all-ambient-types-in-S assumption. The accepted
`SourceEnvironmentComputabilityFormula` has a separate free variable for
each member of an externally fixed Gamma. That paid formula is useful
pointwise, but its changing free-variable arity is not a uniform formula
over all coded contexts. A finite environment-code/lookup bridge is still
required, reusing the existing actual substitution machinery.

The code/graph properties used in these invariants also need PA derivations.
A Lean proof of standard-natural checker calibration is not a constructor
of `InternalCalculus.Derivation`. The calculus deliberately enforces this
remaining boundary.
