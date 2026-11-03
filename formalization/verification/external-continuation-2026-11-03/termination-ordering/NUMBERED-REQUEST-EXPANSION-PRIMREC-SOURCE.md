# Exact request expansion primitive recursion

Paper06 lines551–556 requires effective typed auxiliary syntax. This target proves formal `Primrec` of the existing `NumberedTypedRequests.expand arity`, for every finite ranked alphabet size `n` and every actual arity table `Fin n → Nat`, including `n = 0`.

`NumberedRequestPresentation.RequestData n` is the literal sum `(List Ty × Ty × Code (Fin n)) ⊕ (List Ty × List Ty × Code (Fin n))`. The equivalence maps the original `Request.term` and `Request.arguments` constructors to their unchanged fields. Its `Primcodable` instance is derived by `Primcodable.ofEquiv` from the accepted type, list, and literal numeric code presentations. It does not install a second code encoding or assume a primitive decoder. The standalone presentation imports the accepted `NumberedCodeCodecPrimrecProof` and `NumberedTypedRequestsDefinitions`; it does not depend on the new code-view proof.

The frozen target is the original expansion function, not a new surrogate. Variable lookup uses the same context index and expected type. Lambda expansion rejects ground expected types and mismatched domains, and pushes the actual domain onto the original context. Application produces the same ordered function/argument requests. Bottom and ordinary/numbered heads retain their existing equality tests and actual head-signature functions. The numbered case retains both ordered base and extra argument requests and the original treatment of its numerical label. Argument expansion retains all empty/nonempty-list and constructor mismatch failures and the exact type equality test. Every source `none` case remains `none`.

The candidate proof may decompose one code constructor through the independently frozen literal `NumberedCodeView.view` and its genuine primitive-recursion theorem. The arbitrary finite arity table's primitive-recursion property is derived from its finite domain. No premise supplies expansion, decoder success, or an oracle. This step establishes one-step expansion effectivity; the dependent decoder and bounded worklist evaluator require separate targets and calibrations.

## Accepted verification

The fixed statement gate and the fifteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](TYPED-PRIMREC-FREEZE.json) and
[the acceptance record](TYPED-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
