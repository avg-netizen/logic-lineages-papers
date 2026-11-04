# Actual step substitution with possible equality collapse

Draft requested 2026-11-04 13:14 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

The two targets concern the existing actual WindowStep and WindowArgumentStep under arbitrary typed Substitution Gamma Delta, with symbols/S/above unchanged. Their conclusions are literal substituted equality OR one actual step in Delta. They do not promise a positive step, unchanged positive count, or an arbitrary transitive closure.

Bottom collapse is essential: variable→bottom may become bottom=bottom when the variable is substituted by bottom. At a Bottom root, split on substituted-source equality to bottom; otherwise use the genuine Bottom constructor. Contexts propagate either literal equality or their actual context step. No positive application-argument context is introduced; application has function-side context only. Lambda recursion uses the actual lifted substitution into the binder context.

Constructor correspondence: Put is literal; Select maps its actual packed occurrence using argumentListSubstitute and keeps the complete applyArguments/selfArguments suffix; Copy uses selfArguments substitution and the unchanged headAbove/HeadInWindow guards; Mul uses transported PrimitiveMultiset witnesses, preserving nonempty removal/multiplicity/dominator reuse; Abs uses the exact openNumbered substitution law; beta uses the proved single-environment equation. Ordinary/numbered tuple contexts use the companion induction. Primitive marking is transported only from a successful witness, without a false failure equivalence.

No GoodSubstitution or endpoint confinement is assumed for this raw typed rule compatibility. Any later finite-carrier or numeric statement must separately prove range/endpoint confinement and handle zero-step collapse. No original ordinary-order transitivity, all-term computability, ID1 or unrestricted well-foundedness claim is included.
