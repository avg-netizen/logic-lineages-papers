# Exact lambda and beta-application root reductions

Draft requested 2026-11-04 12:30 UTC. Exact review required before comparator/freeze/proof. Verification-only/no export.

Paper06 lines591–597 discusses lambda computability by reductions of (lambda body) applied to an argument. These targets classify the actual WindowStep constructors, without proving computability. The literal existing relation includes a Bottom rule on every nonbottom term, including a lambda in function position.

First, a step from lam body is exactly either bottom at its arrow type, or lam body' for an actual step body→body' in the binder-extended context sigma::Gamma. Second, a step from app(lam body)a is exactly one of: bottom at result type; the literal actual substitute body (singleSubstitution a); app(bottom arrow-type)a; or app(lam body')a for an actual body step in sigma::Gamma. Both directions are required. Cases are not claimed disjoint, since actual terms may coincide.

The third application case explicitly accounts for function-side lambda→bottom and must not be silently merged with immediate whole-term bottom. The argument remains exactly the same a in both contextual cases. No application-argument positive reduction exists or is introduced.

All quantification is over actual typed terms, arbitrary symbols/arity/window/precedence and contexts. No confinement, subtype closure or ordering assumptions are needed for these raw root statements. Existing actual substitution is merely the beta target; no substitution compatibility, positive-path preservation under substitution, canonical representative correspondence, accessibility, computability, internal ID1 or original-order transitivity theorem is asserted. Exact step preservation under arbitrary substitution would be false because variable→bottom may collapse to bottom=bottom; that separate issue is not hidden in these targets.
