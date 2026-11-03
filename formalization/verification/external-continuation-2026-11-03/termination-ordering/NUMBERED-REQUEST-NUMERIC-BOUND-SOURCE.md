# Literal numeric code bounds structural request work

Paper06 lines551–556 motivates effective typed syntax. This component compares the accepted literal `codeNumber` with the unchanged `codeWeight`, which counts every Code node and both children of binary constructors. All Code values are covered, including ill-typed trees, empty signatures, and zero-valued variable codes. The upper bound is `codeNumber code + 1`; it does not require a validity or decoder-success premise.

`ActualCodeWeightBound` supplies that bound. `ActualCodeFuelPrimitive` establishes that the same bound is a primitive-recursive function under the already accepted Code presentation. The pair-coding constructor tags pay for each removed Code constructor, including both recursive-child contributions.

This supplies a computable sufficient fuel quantity for the separately checked request evaluator. It does not assert that this bound is sharp, that structural node count itself is primitive recursive, that expansion or the full decoder is primitive recursive, or that the full checker, arithmetic representation, accessibility, or whole paper theorem is complete. No accepted parser, numeric encoding, comparison semantics, or target register is changed.

The target file was written before candidate proof authoring; its SHA256 is `0654a5b7dacfb8e8f71de5411920a5a7ad87010c3ea9c8d0b9eab89aad0ef4f0`. Compiler acceptance and actual axiom audits are recorded separately.
## Accepted verification

`NumberedRequestNumericBoundStatementChecks` passed all 2 fixed aliases at the frozen target types.
The focused nine-target aggregate also passed its actual transitive axiom audit
using only `propext`, `Classical.choice` and `Quot.sound`. Current source hashes,
successful module checks and verification scope are recorded in
[the acceptance record](TYPED-VALIDATION-ACCEPTED.json).
