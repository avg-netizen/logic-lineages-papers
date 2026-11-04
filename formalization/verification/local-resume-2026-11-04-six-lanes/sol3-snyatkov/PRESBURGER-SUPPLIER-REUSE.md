# Reuse the accepted general Presburger algorithm

Directly read the accepted public Forests source, not merely a historical
summary. `CotreePresburgerUnitDefinitions` implements finite cutpoint/residue
elimination with the nonnegative witness guard. `CotreePresburgerNormalize`
clears arbitrary signed coefficients using a positive coefficient product and
retains the essential divisibility-by-that-product guard.

`CotreePresburgerDecision` has actual finite-arity first-order affine syntax,
arbitrary Boolean operations and Nat binders. Its actual structural
`quantifierFree` calls that finite eliminator. The exact gate proves
`forall n p v, evalQF (quantifierFree p) v=true iff Realize p v`, where prefix
parameter coordinates range over Int and every binder over Nat. This is the
general mathematical supplier for the Snyatkov linear-only branch, already paid.

The adjacent `CotreePresburgerCompiler` matches the actual pinned Mathlib
Presburger language. `CotreePresburgerFiniteDecision` uses explicit finite
encodings/ordered enumeration, rather than a choice-based finite equivalence.
Those are source syntax/finite-coordinate transports, not an assumed solver.

S3 must still prove an exact bridge: original named variables, finite affine
coordinates, and all dependent nonlinear parameter occurrences must use ONE
original valuation. Pointwise correctness for every Int parameter tuple can
be instantiated at that actual correlated tuple; it does not authorize
independent existential choices for derived values. The output must be put
back into the original shared syntax with correct support and domains.

The read targets do not state a uniform Nat-code `Computable` theorem for the
whole varying-arity algorithm. The concrete numeric encoding/calibration and
effectivity bridge remain actual proof obligations; an executable Lean
definition alone is not being substituted for that S3 contract. Do not rebuild
the mathematical Cooper eliminator or assume its source/code bridge as a field.

Source home, relative to formalization:
`LogicLineages/ModelsAlgebra/Forests/CotreePresburger{Linear,Unit,Normalize,Decision,Compiler,FiniteDecision}*`.
In particular, reread DecisionDefinitions/Targets/Proof/StatementChecks and
NormalizeDefinitions/Targets before using this note as a supplier specification.
All of these accepted sources are read-only to S3.
