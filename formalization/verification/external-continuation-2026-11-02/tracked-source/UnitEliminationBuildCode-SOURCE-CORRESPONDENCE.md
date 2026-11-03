# Uniform numeric original-source unit-elimination builder

Paper 09 `source-realization.tex` lines48–65 recursively removes functional names while preserving shared ground inputs, ending in actual all-ground observation sources. Lines253–256 use this construction for the actual unary ray in the effective head-graph proof.

The numeric builder reproduces the existing typed UnitElimination.build for every fuel, context, output type and actual source, including exhausted or failing branches. It performs the real source type check, first-functional context selection, capture-avoiding selected-slot permutation, exact full-vector OneUnit compilation, and literal ground-block construction. Free/active nodes retain all original fields and ordered children.

Primitive recursiveness uses the existing general finite-descendant recursion theorem with state (fuel, context codes, source code) and measure fuel. Recursive source codes are allowed to grow. Every concrete child/assembly operation is supplied by proved algorithms; no recursive graph oracle or assumed supplier is added.

Fuel context-length-plus-one is discharged by actual typed-source totality. The final target constructs the exact symbolic tree and computable realized numeric tree, proves all source leaves ground-context, and retains the actual complete source-assignment scalar graph under every shared ground valuation. Anchor execution remains only computable.

This closes the raw source-to-unit-tree compilation obligation, not the arithmetic-formula numeric compiler or original paid-head/wire composition. No whole effective head-graph promotion is claimed here.
