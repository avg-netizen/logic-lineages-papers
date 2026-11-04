# Certified precedence chains and primary head classes

Source: 06-godel-t-termination-ordering/paper.tex lines 79–82 (strict ranked precedence and head classes), 543–550 (Copy uses lower precedence), and the subsequent primary-equivalence paragraph. These are properties of the actual head comparison, not of the term rewrite relation.

All four targets assume success of the unchanged finite rank certificate. A finite chain of length k edges is represented by values : Nat → carrier, but only entries 0 through k occur; entries after k are unconstrained and irrelevant. Every nonempty finite sequence has such an extension by repeating its final entry. There is no claim about empty vertex sequences.

Symbol target: k + rank(values k) ≤ rank(values 0), and k<n. Every edge has orientation table(source)(successor)=true, hence successor rank is strictly smaller. For n=0 there is no values : Nat→Fin 0, so the implication is vacuous. Head target uses actual headAbove, proves the same telescoping inequality with headRank, and k≤n+1. For n=0 native→application is still available, giving the correct at-most-one-edge bound. Zero-edge chains are included.

Head-class target calibrates actual RecursiveComparison.headEquivalent exactly to headRank equality. Native constants share rank1, applications rank0; ranked-symbol class equality follows injectivity of the supplied rank. Compatibility then states that replacement of either endpoint by a headEquivalent head leaves actual headAbove unchanged. It does not assert identical term/output types or arbitrary term equivalence.

The bounds apply only to consecutive precedence comparisons. They do not bound WindowStep/R traces, since Put, Select, Mul, Abs and nested steps need not decrease headRank. No global well-foundedness, all-term computability, original-order transitivity, arithmetic/PR or ID1 claim. No proof until exact review and freeze.
