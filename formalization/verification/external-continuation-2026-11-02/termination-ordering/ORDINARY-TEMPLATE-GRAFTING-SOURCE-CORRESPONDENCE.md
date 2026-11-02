# Ordinary template grafting — original weak relation

Source paper06 `lem:graft`, lines447–457: for an ordinary template A and same-type p weak above q, A[x:=p] is weak above A[x:=q], even with marks inside p. The comparison is the original Weak, and substitution is the existing syntactic `substituteTerm` over the embedded ordinary template.

`EnvironmentGrafting` is the actual simultaneous generalization: every template variable is mapped to a same-typed pair in the original Weak. This allows an arbitrary distinguished source variable; it does not assume grafting itself. `DistinguishedVariableGrafting` specializes to the binder variable, preserving all remaining variables identically. Its p and q are unrestricted MarkedTerm values, not required ordinary, normal, closed, confined or already reflexive.

Ordinariness is required only of the template. Its full grammar includes explicit application, lambda, variables, all native constants and ranked arguments. Lambda induction must prove the lifted environment remains pointwise Weak using already accepted renaming covariance; it is not supplied as a new premise. The original source grafting result does not assert support inclusion or arbitrary marked-template monotonicity, and neither do these targets.

This is a prerequisite for beta orientation with the selected self-copy as p and the original ordinary argument as q. It is not a theorem that arbitrary Weak derivations are preserved under arbitrary substitutions. Full numbered promotion requires both targets and complete covariance dependency closure accepted.
