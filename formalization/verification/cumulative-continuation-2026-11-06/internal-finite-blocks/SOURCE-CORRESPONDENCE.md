# Exact finite compiler blocks in the original calculus

Baseline: `2066300c16197fc71dc30c87d61fb6bb11eadd9b`. Original ordinary
arithmetic graphFormula compiles composition using existsFin and andFin, and
recursion using the same finite blocks with beta graphs. Existing calibration
is standard-N semantics, not an internal derivation. This supplier proves
finite-block syntax and logical admissibility from the existing singleton
rules and accepted proof-tree renaming, without adding a block constructor.

Five frozen targets cover exact empty/last-binder identities and Fin order,
commutation with the original arithmetic embedding, actual existential block
introduction/elimination, and the original andFin conjunction. Zero-sized
blocks/tuples are included. The fresh-variable elimination premise remains
an actual original Derivation; it is not replaced by semantic implication.
The block abbreviation is literally the existing relabel/exs expression,
and a separate equality pins it to the ORIGINAL OrdinaryArithmetic.existsFin.

This is a prerequisite for exact original graph composition, not a proof
of that later consumer, arbitrary PR recursion representability, encoded
typed-preservation/application, C_tau closure, all-term accessibility or whole
lem:id1. No arithmetic reflection, extra calculus rule, II5 or well-foundedness
claim. No existing target/source, manuscript, register, checker, dependency,
root import or CI change. Frozen syntax/targets precede candidate proof.
