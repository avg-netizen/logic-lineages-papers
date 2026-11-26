# Literal binary constant Plan lowering

The printed compiler pays binary constants using a shared doubling and
add-one sequence. The actual typed implementation is
`BinaryPlan.constantPlan`. It shifts its one continuation under every
fresh predecessor and retains it once. This comparator uses the existing
checked binary halving trace, whose parity list is inner-to-outer and whose
reconstruction is the actual `binaryDAG`.

The raw compiler reads that list in reverse, so each step treats the
outermost pending binary constructor. A double adds one fresh binder,
two shared references to the predecessor and one add gate. A double-one
adds three fresh binders, two adds and one one gate. The exact proof
uses the actual continuation renaming at the same enlarged context.
The terminal zero or one emits the corresponding actual gate. A tracked
prefix count emits all binders at their original positions before the
remaining spine. The arbitrary-trace calibration explicitly includes
both branches of every raw parity and base code, matching the concrete
reconstructor.

The final constant matches the exact encoded typed Plan for every Nat,
context and continuation and the numeric-list routine is jointly primitive
recursive. The numeric work decodes binary syntax. The theorem uses no
source evaluation and leaves Boolean lowering and whole-input validation
to separate comparators.
