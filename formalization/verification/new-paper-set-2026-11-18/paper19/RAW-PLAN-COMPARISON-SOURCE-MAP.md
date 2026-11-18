# Final comparison outputs on raw Plan codes

This supporting packet composes the raw Plan compiler and literal checked
detector aggregation and wrappers. Its typed endpoint is the exact pair of
typed outputs from `ExistentialPlan.strictPair` and
`ExistentialPlan.weakPair`. The first comparison reverses the aggregate
pair as in the typed implementation. The second wraps the strict left
output with the actual upper wrapper and the strict right output with
the actual lower wrapper.

Every successful raw call reconstructs the original Plan in one typed
context and the literal output DAG codes for both comparisons. Computing
the raw outputs uses sequential checked finite operations. It performs
no numerical source evaluation. This packet starts with the raw Plan
syntax and leaves the complete arithmetic and Boolean frontend to a
separate exact comparator.
