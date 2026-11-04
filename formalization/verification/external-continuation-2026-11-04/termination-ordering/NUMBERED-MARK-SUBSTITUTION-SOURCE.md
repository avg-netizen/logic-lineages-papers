# Success-only primitive marking substitution

Draft requested 2026-11-04 12:41 UTC. Exact review/comparator/prospective freeze required before proof. Verification-only/no export.

The targets concern actual NumberedRewriteReduction finiteMark, PrimitiveMark and PrimitiveMultiset, the witness relation of the actual guarded Mul constructor. They are a prerequisite for lambda-instance reduction compatibility, not that theorem itself.

Target one preserves a successful finiteMark with its same finite label and exact substituted output. The lambda case must use actual lifted substitution. No failure preservation or iff is asserted: a variable initially has finiteMark=none but may be substituted by an ordinary head that can be marked. Target two packages this same-label success transport as literal PrimitiveMark on mapped packed terms.

Target three maps an actual PrimitiveMultiset witness: kept, removed and inserted lists are each mapped occurrence by occurrence. List permutations are preserved, removed remains nonempty because mapping does not delete entries, and every inserted occurrence retains a marked removed dominator via target two. Distinct occurrences may become equal under substitution; their multiplicities remain and no injectivity is assumed. A single removed occurrence may continue to dominate multiple inserted occurrences, exactly as in the original relation. No new target occurrence or witness is invented.

These raw typed statements quantify arbitrary Symbol/arity and typed Substitution Gamma Delta; no finite-window confinement premise is required. Later finite-carrier results must separately use actual range confinement. No positive-step substitution compatibility, preservation of positive count, beta composition, original-order transitivity, computability or ID1 theorem is included.
