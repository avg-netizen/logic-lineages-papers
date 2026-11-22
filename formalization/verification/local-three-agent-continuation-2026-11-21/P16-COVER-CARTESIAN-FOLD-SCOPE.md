# Ordered Cartesian fold for the physical cover lists

`NumberedWindowInternalCoverCartesianFoldChecks` passed native gate `1795333143055466470-9` with 2334 local modules and two exact aliases using only standard axioms. Earlier exact source and compiler diagnostics are retained.

The numerical law computes the actual ordered flat-map under the original standard scratch list code. The physical list recursion calls the given block program at each source occurrence, appends the block before the recursive tail, and thereby preserves repetitions and order.

The open proof establishes membership in the given physical output from actual membership of a chosen source entry and actual membership of the image in that entry's computed block. It uses object list induction, the true cons membership cases and the original left and right append introductions. Proof contexts, list terms, parameters and entry terms are arbitrary. Specializing all four axes and integrating the original grammar stage are separate.
