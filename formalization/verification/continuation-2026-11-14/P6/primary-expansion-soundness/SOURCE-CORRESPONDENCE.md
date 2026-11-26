# Exact internal semantics of original one-step reachability

Original ContextUniformPrimary.step is reached ++ pool.filter(any reached E).
The paid literal Programs already calibrate this exact operation, preserve old
membership and introduce every actually accepted edge. The missing converse
is whether every newly emitted member really has an old-source edge witness.

Four exact contracts close that internal semantic gap: any acceptance yields
an actual existential source with membership/E graphs; filtered membership
yields literal pool membership and old-list any acceptance; appended membership
yields left-or-right; expansion membership is exactly old membership or a pool
member with an existential old-source accepted edge. Existentials/disjunctions
are inside the original first-order calculus, not external model facts.

Use existing listRec and codec inversions and strong induction on arbitrary
runtime numeric list codes. Preserve exact-one tests, old reached, repetitions,
ordering, nil/default behavior and original ASTs. No new E correctness premise
is claimed: E is generic and all edges here are its ACTUAL internal graph.

This supports an eventual path/finite-closure argument without choosing a new
cutoff. Still missing: structural correctness of selected original E, proof
that pool enumeration has needed original vertices, internal stabilization at
literal vertices.length, row coherence and original stable-source issues.
No native calibration is reflected into internal derivations. No source target
or prior checked proof changes, and no proof before reviewed native preflight.
