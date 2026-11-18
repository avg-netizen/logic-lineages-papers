# Actual unchanged-G application and eraser bridge

Concept proposal before freeze/proof, supporting the unchanged-G dependency route for cor:standard-functional-hardness. StandardSourceFacts and StandardDetectorNumeric are independently accepted. No detector or hardness conclusion yet.

## Inspected implementation and permitted reuse
SelectedDetectorApplicationProof.unary_app_value is genuinely arbitrary-control/arbitrary-policy syntax evaluation, with explicit successful child vectors and finite scalar calibration; it has no selected-admission premise. Its later unaryApp and eraser_value theorems DO require selected admission and cannot be instantiated at Phi. Reconstruct those later arguments using actual StandardSourceFacts success and scalar calibration.

SelectedHardnessCombinatorSyntaxProof.app_assignment and SelectedHardnessUnusedProof.unused_assignment are actual all-policy literal assignment identities. SelectedHardnessScalarSyntaxProof.repeated_value is arbitrary-control finite scalar arithmetic. These can be reused as syntax/calibration suppliers, not as selected semantics. Alternatively copy the small unary_app_value argument into the fresh proof to keep the control boundary visible.

Actual eraser syntax is SourceCollisionCompletion.eraser a b, the application of an unused-binder abstraction to b. The local positive coordinate equals one for every allowed policy, by the literal singleton shape. Scalar coordinate of that abstraction is 3*A+2, paid by its repeated scalar tree plus retained addend, not by a default-policy computation. The final value is collapseWith Phi(omega+(3*A+B+2)).

## Proposed exact supporting endpoint
For every context, arbitrary policy and actual Phi-admissible substitution, no bounded-input or successful-assignment premise:

1. Actual ground zeroC has a successful assignment and scalar value1 (including groundValue=1).
2. For arbitrary unary a and ground q, actual application has a successful ground vector, positive finite scalar equal to its actual groundValue, and exact groundValue equality to StandardDetectorNumeric.appValue(value1 a,value0 a,groundValue q). Thus the earlier numeric function is now tied to a genuine source application. All child positivity/finite values come from StandardSourceFacts.
3. For arbitrary ground a,b, literal eraser has a successful ground vector and positive finite scalar equal to actual groundValue, together with the exact actual Phi collapse expression above. All unused-binder and retained-coordinate steps explicit.

Success and positivity must be conclusions, not caller-supplied fields. Finite-value/card/norm are already paid by StandardSourceFacts and may be bundled with each output if useful.

## Follow-on work and exclusions
Next a distinct combinator-coordinate packet will reconstruct actual all-policy pad/combine/head identities at Phi from the audited syntax roots; then fresh shared-payload/detector comparison and alignment can compose with the accepted numeric source bridge. This packet does not assert those identities, vector alignment, complete detector, finite-query reductions or unchanged-G hardness. No SelectedWithThreshold Phi, no selected modular CountLag, no default-policy source theorem transfer. Threshold route remains parked.
