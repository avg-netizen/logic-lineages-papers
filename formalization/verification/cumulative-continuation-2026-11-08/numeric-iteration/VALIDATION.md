# Numeric iteration validation and consumer API

All four frozen targets passed their exact aliases and actual axiom audits.
The only permitted axioms used are `propext`, `Classical.choice`, and
`Quot.sound`. The separate definitional stack-iterator identity compiled and
its actual axiom closure is `[propext]`.

The main consumer import is:

    LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof

It exports these four exact original-calculus theorems from namespace
`InternalNumericIterationProof`:

- `actualOriginalNumericIterationZero`
- `actualOriginalNumericIterationFrontSuccessor`
- `actualOriginalNumericIterationAdditionFusion`
- `actualOriginalNumericIterationFixedPoint`

Their target types and all quantifiers remain exactly the frozen ones.
Reusable derivation-transforming helpers retain arbitrary contexts and
arbitrary symbolic terms:

- `InternalNumericIterationSupportProof.repeatZeroValue`
- `InternalNumericIterationSupportProof.repeatZeroRecover`
- `InternalNumericIterationSupportProof.repeatSuccValue`
- `InternalNumericIterationSupportProof.repeatSuccRecover`
- `InternalNumericIterationProof.frontSuccForward`
- `InternalNumericIterationProof.frontSuccBackward`
- `InternalNumericIterationFusionProof.fusionValue`
- `InternalNumericIterationFusionProof.fusionRecover`
- `InternalNumericIterationFixedPointProof.fixedValue`

`InternalNumericIterationStackCompatibilityProof.stackIteration` proves by
reflexivity that specialization at the original stack transition is the
already frozen concrete stack iterator. Its module imports stack definitions
only and is separate from the generic proof supplier.

The front-successor argument uses the original natural-induction constructor
with four states universally quantified inside the commutation invariant.
Fusion uses original natural induction in the second count, with first count
and all states universally quantified inside its invariant, and only the
original addition-zero/successor laws. Fixed-point stability uses original
natural induction in the same arbitrary context. Both reverse equivalence
directions use the already proved original program totality/functionality.
No semantic-reflection principle or new premise is introduced.

There are 1,065 local modules in the exact-check plus preflight import closure.
Every current source hash matches a successful native compiler receipt.
The full local receipts, source-to-receipt matches and seven candidate
snapshots are retained locally. Failed candidates 003, 004 and 006 remain
unaccepted: respectively a missing local-abbreviation unfolding, an unused
unknown simplification identifier, and an audit command aimed at an imported
rather than locally declared namespace. Repairs did not change any frozen
specification or mathematical statement. Candidate 007 passed the exact gate.

The independent specification review was accepted before the successful
native preflight, and mathematical proof authorship began only afterward.
All original pins and frozen specification/correspondence bytes remain
unchanged. The historical pending status in the immutable freeze describes
the earlier freeze, not the current checked state.

This package proves iteration algebra only. Worklist append/decomposition,
payload termination, sufficient-fuel stability, the recursive validator's
calibration and internal application-validity constructor law remain
separate consumer obligations. No numbered source statement is promoted.
All owned compiler jobs are reaped, both shared locks are free, and the sole
compiler slot has been released. No full-root build, remote CI or Git action
is claimed.
