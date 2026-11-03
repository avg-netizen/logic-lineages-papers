# Bounded evaluation of actual finite-universe requests

Paper06 lines537–540 fixes the finite type universe for numbered auxiliary
syntax, and lines551–556 requires computable classes and arithmetic relations
before taking least-code representatives. This component evaluates the original
finite-universe tests after the original typed decoders, using the existing
requests and their literal expansion. It changes none of those semantics.

`NumberedUniverseRequests.valid` means that the actual term or argument decoder
succeeds and that its returned object passes the original `universeTest` or
`argumentsUniverseTest`. Its independent root guard checks each term's result
type, the domain annotation at a lambda, and the original head-window condition
at ordinary and numbered heads. Argument-list requests contribute no new local
condition. In particular, the evaluator imposes no requirement on unused context
entries, and an empty argument list contributes no blanket type-list condition.

`evaluate` returns true for empty work even at zero fuel, and false for exhausted
nonempty work. At positive fuel it checks the actual universe root guard. A false
guard or failed original typed expansion returns false. Successful expansion
places the ordered children before the pending suffix and consumes one fuel unit.
No transition invokes the recursive decoder or its semantic validation function.
The same node weights as the previously accepted typed evaluator count every
recursive child occurrence, including repeated occurrences.

`State` is exactly `Option (List (Request n))`. The literal `step` makes failure
`none` and completion `some []` absorbing. `run` applies that step exactly the
specified number of times, and `done` tests for the completed successful state.
These auxiliary definitions expose ordinary finite iteration for the effectivity
target without modifying the recursive evaluator.

The four frozen statements require soundness at every fuel, exact agreement
with all actual semantic validations once the original total request weight is
available as fuel, exact iteration/evaluator calibration at every fuel, and
primitive recursiveness of the evaluator jointly in both finite window lists,
fuel, and the entire genuine request list. Each signature size and its actual
arity function are fixed parameters universally quantified by the effectivity
target. The empty signature, arbitrary contexts, malformed or mistyped codes,
empty windows, and arbitrary insufficient fuel remain in the domains. No
subtype-closure, initial-validity, expansion-effectivity, or guard-effectivity
hypothesis is added to any target.

The independent one-layer calibration is required for the semantic proof. The
primitive-recursive proof must use the actual expansion's checked effectivity
and the independently established effectivity of the actual root guard, then
primitive-recursive list/option operations and finite iteration. These are proof
dependencies, not assumptions replacing the requested result.

This component is a bounded finite-universe evaluator. It does not by itself
assert primitive recursiveness of the packed term universe test, the raw or
canonical numeric carrier, class enumeration, least representatives, the full
step checker, arithmetic representability, ID1 accessibility, or a whole paper
theorem. Those applications require their own exact calibration and integration.
The source-statement register is unchanged.

## Prospective statement freeze

The following hashes were recorded before candidate proof authoring. Comparator
compilation and later acceptance evidence are separate integration records.

| Source | SHA-256 |
|---|---|
| `NumberedNumericCarrierDefinitions.lean` | `ee403826c88c271dc470928ab320a0461981abd974873bf7b05cd646ad475de7` |
| `NumberedUniverseRequestsDefinitions.lean` | `3d7e1e4a928a47660c5ec3d6078574ab3497f5bce37a9267e9b40aa57e9f9589` |
| `NumberedTypedRequestsDefinitions.lean` | `78f51decd6d5daaa58329eafd57a392b28a2a38b6fcd656b9cf39e8fe44fcb84` |
| `NumberedRequestWeightDefinitions.lean` | `9c3ecde668708ebf9648710aef446a7e0da5984cfb9701c7100481b6c2d7bc2b` |
| `NumberedRequestPresentationDefinitions.lean` | `3da2e6a6e9225cd00912bd9825a86e3c86a09e23374a925be8d603dd96ca0540` |
| `NumberedUniverseEvaluationDefinitions.lean` | `35ed949f1de24568ca440817ab037372c3cf5601d280d8096e1f8c5ed1c138a1` |
| `NumberedUniverseEvaluationTargets.lean` | `744f0f330f5a1ca044419f2ec5ebabb63d30a60170d1f7580b4ee071e86cb892` |
| `06-godel-t-termination-ordering/paper.tex` | `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e` |

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](UNIVERSE-PRIMREC-FREEZE.json) and
[the acceptance record](UNIVERSE-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
