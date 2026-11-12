# Concrete evaluator design after the checked native raw-work bound

Status: proposal, not an implemented evaluator or integration claim.

## Reuse and the non-circularity constraint

The checked structural-node machine supplies the literal raw eight-constructor dispatch, first/second selectors, work-stack shape and native/raw internal recurrence proof patterns. Existing all-position selectors supply actual cutoff lookup, deleteAt, erasedPacked and unchanged left parameter. DeletionRows supplies a bounded ordered scan and actual indexed extraction. TypedArgumentObservations supplies tagged argument-spine walking and order-preserving collection. NumericListSort supplies actual insertion-sort AST and native calibration.

These do not combine by setting Q to the evaluator being defined. rootObservation Q and rows Q contain Q as a literal Program subterm; substituting the new evaluator into itself would be circular. A genuine evaluator must enqueue recursive work and assemble returned observations from an explicit value stack. The arbitrary-Q layer remains a useful equation to prove about that scheduler, not a recursive Program definition.

## Proposed state and scheduling

Use a tagged work stack plus a result stack. A visit frame records raw code, original context code, unchanged original window code, semantic role (term versus argument-list), outer type when it is a term, depth, and return continuation. A return frame records the constructor metadata and number/order of values to consume.

On visit, enqueue actual raw constructor children in first/second order and every actual context deletion in increasing cutoff order. Each occurrence gets its own job; neither repeated children nor equal context entries are deduplicated. Lambda's body job extends Gamma with the actual domain and its deletion enumeration begins at zero. BASE and extra argument-list spine nodes are explicit jobs, matching the checked raw-work tree. BASE order is a scheduling order only; the return phase sorts the typed BASE observations, while preserving application order and numbered-extra order.

There must be a separate exact invariant explaining which list-node return values constitute the parent's child-observation list. A deletion of an argument-list work state is part of the deliberately larger raw tree; either compute its well-defined list observation or explicitly prove a scheduler pruning simulation before omitting it. Do not call it an observation of a typed term.

## Three different cost accounts

1. Abstract visit count: already bounded for the exact raw child-plus-all-deletions tree by budget(weight+2,weight). The checked terminal-frontier property prevents depth truncation.
2. Scheduler macrosteps: count each push/pop, one list-cons/append/reversal iteration, and each insertion-sort iteration explicitly. This is NOT automatically the visit count. Per node, at most weight context rows occur; raw argument spines and typed BASE lists have length bounded by nodeCount. A direct insertion sort of m elements uses a quadratic number of list traversal steps; these steps need an explicit recurrence theorem for the existing sort/insert AST. Existing bounded argument walking uses numeric-code-plus-one fuel, not a proved structural-length fuel: that bound must be retained or replaced only after a new proof.
3. Primitive arithmetic/Program evaluation cost: numeric pairing, comparisons and a preexisting representative R can cost much more than one scheduler step. Treating a total calibrated subprogram as an atomic macrostep is valid for scheduler fuel, but does not bound its interpreter instruction count or wall time. Such a bound needs a defined cost model and separate size/cost calibration. No current theorem supplies it.

## Smallest next frozen operational contract

Build a standalone ONE-NODE expansion Program, not the evaluator. Inputs encode the actual raw code and original Gamma; the original window code is carried unchanged. Output is the encoded ordered list of raw-state jobs:

    children Gamma code ++ deletionsFrom code [] Gamma

Use existing arity/first/second selectors for the first list and a primitive-recursive context-length scan for the second. A deletion job uses the actual lookup type, original arbitrary-cutoff raw erasure, and actual deleteAt context. On genuine Code inputs its exact native output must equal map(stateNumber)(WorkBound.successors state), including duplicates and cutoff zero. A separate theorem records actual job-list length and the checked weight decrease of each decoded job. Malformed numeric behavior must be fixed in the AST and separately described, not inferred from typed calibration.

Only after this expansion contract is verified should a small stack transition be frozen: visiting one frame schedules exactly that list and one return frame; it performs no recursive evaluation. Prove a work-stack potential using the checked full-subtree visit budget plus explicitly counted administrative frames. Return assembly, argument collection and sort loops then get their own transition accounting before selecting the final machine fuel.

## Explicit limits

No total evaluator AST, no concrete transition fuel, no primitive-cost bound, no full HereditaryView equivalence, no internal class-uniformity law, and no existing source/minimum/final tuple change are claimed by this design.
