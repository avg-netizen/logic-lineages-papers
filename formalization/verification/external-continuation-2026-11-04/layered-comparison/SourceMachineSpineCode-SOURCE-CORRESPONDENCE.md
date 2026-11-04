# Explicit machine conjunction spine constructor

This constructor encodes the unchanged SourceMachineConjunctionPlan.plan for the literal arithmetic conjunction in paper09 hardness.tex lines 294–314. It composes accepted numeric scaling and binary CPS builders without evaluating Gamma or halting. Input b enters only the literal coefficient C=2*b+5; e controls doubling.

ExactSpine states literal list equality to the existing canonical spine and the actual Supported property. In the thirteen-wire context, zero-based source positions 0..12 become one-based port numbers 1..13. Initial additions use (10,10,1) and (1,9,2), scaling maps port2 to3, then the fixed continuation uses (11,8,4), equality(4,3), (13,13,5), (5,7,6), equality(12,6), and source successorCode11 = portCode12. The last two values are actual source-term codes, not raw port numbers.

Three constant wrappers are nested in original C,4,1 order around six existential intermediate wires. Each wrapper adds its own constant binder and invokes the literal binary builder with output port1; its continuation already lies in the extended context and is not spuriously shifted again. All per-gate local-one allocation and deeper binder insertions remain those of the accepted binary/scaling builders.

ExactOutputs calibrates the compiled witness count and exact ordered forest of encoded source pairs, plus the actual aggregate codes in (L,R) orientation. The eventual strict semantic comparison is R<L; this component does not silently swap the aggregate or add a decision theorem.

UniformPrimitiveRecursive covers constant wrapper, tail and the complete (b,e)-to-spine, compiled-state and aggregate-pair maps on all naturals using standard Primcodable lists/products. No scalar Nat wrapper, malformed-code validity, source complexity or runtime bound is claimed. This is not a whole source hardness/completeness promotion. All existing sources/frozen packages stay unchanged; verification-only, no export.
