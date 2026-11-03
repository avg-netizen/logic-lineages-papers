# Fuel-bounded evaluation of actual typed decoder requests

Paper06 lines551–556 requires computable auxiliary syntax classes before taking
least-code representatives and an arithmetic step relation. This component
continues the actual typed decoder interface: it does not change auxiliary
syntax, the mutual decoders, accepted one-layer request expansion, or structural
weights.

`evaluate` is a direct bounded worklist interpreter. The empty list succeeds,
including at zero fuel. A nonempty list with zero fuel fails. At positive fuel,
a failed actual local expansion fails; a successful expansion replaces the
first request by its ordered children before the unchanged pending suffix.
The evaluator does not call the original recursive decoder or a supplied
semantic oracle.

The four frozen targets are: soundness at every fuel; exact equality with the
conjunction of actual decoder successes when fuel is at least the total Code
node weight; exact term success at its own Code weight; and exact argument-list
success at its own Code weight. Bounds count each repeated child occurrence.
Contexts, binder extension, signatures, type mismatches and malformed constructor
cases are inherited from the unchanged actual request expansion. The signature
size is arbitrary, including zero. No validity premise is imposed on inputs.

This is a total executable Boolean success evaluator with an explicit sufficient
fuel bound. It is not yet a proof of primitive recursiveness, a dependent typed
output presentation, full step-checker effectivity, arithmetic representability,
ID1 accessibility, or a whole source theorem. The global register is unchanged.

## Prospective statement freeze

The following hashes were recorded before candidate proof authoring. Comparator
compilation and later acceptance evidence are recorded separately by integration.

| Source | SHA-256 |
|---|---|
| `NumberedTypedRequestsDefinitions.lean` | `78f51decd6d5daaa58329eafd57a392b28a2a38b6fcd656b9cf39e8fe44fcb84` |
| `NumberedTypedRequestsTargets.lean` | `5be5a7498428e8a3ebc39dd832ebe4dbb789336c7b659c0d7ef008c64cd18702` |
| `NumberedRequestWeightDefinitions.lean` | `9c3ecde668708ebf9648710aef446a7e0da5984cfb9701c7100481b6c2d7bc2b` |
| `NumberedRequestWeightTargets.lean` | `32370dbb75869a1557792e2bc0048abb23e1239ac0611d69906d775918c02133` |
| `NumberedTypedEvaluationDefinitions.lean` | `d90ce0f736e6effb0b653f75a4dba82b85b0daf3705724f6cb986c62fee60b92` |
| `NumberedTypedEvaluationTargets.lean` | `d674545ee549f502c21dc0a05a383874f15247c64f4e46c0a7dae5449b944bd5` |
| `06-godel-t-termination-ordering/paper.tex` | `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e` |
## Accepted verification

`NumberedTypedEvaluationStatementChecks` passed all 4 fixed aliases at the frozen target types.
The focused nine-target aggregate also passed its actual transitive axiom audit
using only `propext`, `Classical.choice` and `Quot.sound`. Current source hashes,
successful module checks and verification scope are recorded in
[the acceptance record](TYPED-VALIDATION-ACCEPTED.json).
