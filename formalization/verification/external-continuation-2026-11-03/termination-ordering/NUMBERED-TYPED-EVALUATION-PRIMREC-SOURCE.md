# Primitive-recursive evaluation of actual typed decoder requests

Paper06 lines551–556 requires computable auxiliary syntax classes and arithmetic
relations on their least-code representatives. This component supplies the
primitive-recursive bounded evaluator used by the already checked actual typed
success validation. It leaves every accepted request, decoder, expansion,
structural weight and evaluator equation unchanged.

The state is literally `Option (List (Request n))`. A single `step` sends failed
state `none` to itself, completed state `some []` to itself, and nonempty work to
the actual first request's successful ordered children followed by the unchanged
pending suffix. An actual failed local expansion becomes `none`. `run` iterates
this transition exactly `fuel` times. `done` is true exactly for `some []`.
No step invokes the recursive typed decoder or a semantic oracle.

The first frozen target equates `done (run arity fuel requests)` with the exact
accepted `evaluate arity fuel requests` for every fuel and every pending request
list. It covers empty work at zero fuel, exhausted nonempty work, failed local
checks, early completion, repeated children and arbitrary contexts. The second
target proves the accepted evaluator itself primitive recursive jointly in its
fuel and worklist inputs under the genuine field-preserving Request presentation.
Each finite signature size and its actual arity function are fixed parameters;
the theorem is universal over their choices, including the empty signature.

The proof must derive one-step effectivity from the actual expansion theorem,
then use ordinary primitive-recursive iteration on the genuine encoded state.
Expansion effectivity is not a premise of either accepted target. The independent
Request presentation and expansion components retain the actual type, context,
code and child ordering. The previously checked sufficient-fuel theorem and
numeric node bound are separate unchanged results.

This is bounded evaluator effectivity. It does not by itself establish a
primitive-codable dependent typed output, full step-checker effectivity,
arithmetic representability, ID1 accessibility, or a whole paper theorem.
The source-statement register remains unchanged.

## Prospective statement freeze

The following hashes were recorded before candidate proof authoring. Comparator
compilation and actual acceptance are recorded separately; the full dependency
closure also includes the independently frozen Request presentation.

| Source | SHA-256 |
|---|---|
| `NumberedTypedRequestsDefinitions.lean` | `78f51decd6d5daaa58329eafd57a392b28a2a38b6fcd656b9cf39e8fe44fcb84` |
| `NumberedTypedEvaluationDefinitions.lean` | `d90ce0f736e6effb0b653f75a4dba82b85b0daf3705724f6cb986c62fee60b92` |
| `NumberedTypedEvaluationTargets.lean` | `d674545ee549f502c21dc0a05a383874f15247c64f4e46c0a7dae5449b944bd5` |
| `NumberedTypedEvaluationPrimrecDefinitions.lean` | `833c94abc4903bc6740ad0e8ef5b6aa938b06437b29f25bd3efd495be183a5b2` |
| `NumberedTypedEvaluationPrimrecTargets.lean` | `c61de3aa71cf9f9663bc6b69c327640ad5e801ae021bc5e0ced9d4a1922b45ba` |
| `06-godel-t-termination-ordering/paper.tex` | `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e` |

## Accepted verification

The fixed statement gate and the fifteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](TYPED-PRIMREC-FREEZE.json) and
[the acceptance record](TYPED-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
