# Original-spine plan review

Approved in principle for exact definitions/target freezing, not yet a final
implementation review. The locally nameless carrier is a distinct planned
representation rather than a mutation of the accepted named syntax.

Inspect original residual BEFORE substitution, accumulate consumed arguments in
reverse binder order, and never continue consuming freshly exposed lambdas from
an inserted argument. Substitution under binders must use exact depth-dependent
lifting and lower surviving outer indices by the substituted block length.
Check original residual function suffix types for the remaining tuple.

S is a valid concrete functional ordinary head for the printed counterexample:
(lambda x:(o->o).x) has type (o->o)->o->o, so the full tuple[S,y] is typed.
Its original variable residual blocks; staged unary calls can succeed. Do not
claim ordinary associativity or successful substitution covariance from this
example. Typed preservation, alpha correspondence and full relation remain
separate exact proof obligations. Re-review the actual definitions before proof.
