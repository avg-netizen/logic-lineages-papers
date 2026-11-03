# Primitive-recursive one-layer view of actual auxiliary Code

Paper06 lines551–556 requires effective arithmetic treatment of the numbered auxiliary syntax. The accepted recursive `Code` already has its literal numeric presentation. This component exposes one constructor layer as a finite sum of field products while retaining that presentation and every recursive Code child unchanged.

The eight branches are, in order: variable index; lambda domain and body; application domain, function and argument; bottom result type; ordinary head and base; numbered label, head, result type, base, ordered extra types and extras; empty arguments; and argument-cons type, head and tail. The sum and all products are right associated. No field, occurrence, binder annotation, label, or ordered child is discarded. The branch for an empty argument list has the unique Unit payload.

`ActualViewRoundTrip` requires exact inverse equations in both directions. `ActualViewPrimitive` requires that this literal case-analysis map is primitive recursive under the previously accepted Code presentation. No new encoding for Code is installed. The numeric proof implementation may use total defaults when inspecting arbitrary natural numbers; calibration must reconstruct the exact literal view on every actual Code through the accepted decoder round trips. Empty signatures and ill-typed Code values remain included.

This component establishes effective constructor inspection. It does not establish primitive recursiveness of request expansion or full typed validation, a dependent typed-output presentation, full step-checker effectivity, arithmetic representability, accessibility, or a whole source theorem. The accepted syntax, decoders, comparison semantics, and target register remain unchanged.

## Prospective statement freeze

These files were written before candidate proof authoring. Comparator compilation and later acceptance are recorded separately.

| Source | SHA-256 |
|---|---|
| `NumberedCodeViewDefinitions.lean` | `ce60536dc66672ac132ceec8a2f8eb2ed4742202c13aec485a15b1ba25cefaa1` |
| `NumberedCodeViewTargets.lean` | `9d05fd425dc38c27809f4b78d3675f239aa944f0c2fd040cde6ebf42e820d860` |

## Accepted verification

The fixed statement gate and the fifteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](TYPED-PRIMREC-FREEZE.json) and
[the acceptance record](TYPED-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
