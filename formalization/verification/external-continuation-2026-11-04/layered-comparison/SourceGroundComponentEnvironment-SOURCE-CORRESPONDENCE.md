# Sparse ground-component environment

Target-only proposal for the finite raw valuation representation used by paper09 hardness.tex lines316–319 and paper.tex lines30–43. Natural raw values are used directly; positivity, when required by the source comparison, remains a separate valuation premise.

The input list is in de Bruijn variable-index order. Its sparse output environment has length one plus the maximum code Nat.pair j 0 for j<input length. Each slot k decodes both coordinates: nonzero component index returns zero, while component zero reads input variable index with explicit zero default. This keeps the exact existing componentCode representation rather than treating variable position as the component code.

ExactLayout proves length, every in-range ground slot lookup, and zero at every nonground component slot (including outside the allocated range). TypedLookup requires AllGround Γ and exact input length Γ.length, which ensures actual coordinates are zero and actual variable indices are in range. It identifies the output lookup with the explicit rawValuation function. UniformPrimitiveRecursive is independent of any control function or source evaluator.

No assignmentCode composition, arbitrary-context higher-coordinate semantics, positive-output claim, whole-source evaluator, source upper bound/completeness, runtime or publication is asserted. Existing syntax, assignments and encoding remain unchanged.
