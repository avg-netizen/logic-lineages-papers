# Actual numeric typed-syntax validation

Paper06 lines551–556 uses computable primary classes, least-code representatives,
and arithmetic relations on numbered auxiliary syntax. This component connects
the bounded request evaluator to the accepted numeric syntax decoders. It leaves
the manuscript, coding, typed syntax, mutual decoders, and validation filters
unchanged.

The new term and argument-list validators first run the existing numeric Code
decoder and then traverse the actual typed requests with fuel `value + 1` read
directly from the input natural number. The packed validator reads the original
type/code pairing and applies the term validator. None of these Boolean
validators calls the dependent term or argument decoder. All natural inputs are
covered, including malformed Code encodings, ill-typed syntax, type/signature
mismatches, arbitrary binder contexts, and the empty finite signature.

The three fixed targets compare these functions with the success of the actual
numeric/typed decoder composition. The packed target includes the accepted final
`packedNumber = value` filter; proving only success of the unfiltered parser
would not satisfy it. The implementation has no assumed typing, validity,
subtype-closure, or fuel-adequacy premise.

The sufficient numeric fuel is justified separately by the actual Code-node
weight bound, and the worklist evaluator by its exact sufficient-fuel theorem.
This component proves Boolean validation correctness, not primitive recursiveness
of the complete validator, a primitive-codable dependent typed output, full
step-checker effectivity, arithmetic representability, accessibility, or a whole
paper theorem. The source-statement register remains unchanged.

## Prospective statement freeze

Recorded before candidate proof authoring; comparator compilation and acceptance
are recorded separately.

| Source | SHA-256 |
|---|---|
| `NumberedNumericTypedValidationDefinitions.lean` | `2b7343292ef6e098b75931ff318e219684f9bfb649a5a9cb0dd973d08801c3b2` |
| `NumberedNumericTypedValidationTargets.lean` | `c63843069bfc005bd3ce29ffbf0787dbdf3f294ebd3cddb71b165e4e41ae975a` |
| `NumberedTypedEvaluationDefinitions.lean` | `d90ce0f736e6effb0b653f75a4dba82b85b0daf3705724f6cb986c62fee60b92` |
| `NumberedTypedEvaluationTargets.lean` | `d674545ee549f502c21dc0a05a383874f15247c64f4e46c0a7dae5449b944bd5` |
| `NumberedRequestNumericBoundTargets.lean` | `0654a5b7dacfb8e8f71de5411920a5a7ad87010c3ea9c8d0b9eab89aad0ef4f0` |
| `06-godel-t-termination-ordering/paper.tex` | `bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e` |
## Accepted verification

`NumberedNumericTypedValidationStatementChecks` passed all 3 fixed aliases at the frozen target types.
The focused nine-target aggregate also passed its actual transitive axiom audit
using only `propext`, `Classical.choice` and `Quot.sound`. Current source hashes,
successful module checks and verification scope are recorded in
[the acceptance record](TYPED-VALIDATION-ACCEPTED.json).
