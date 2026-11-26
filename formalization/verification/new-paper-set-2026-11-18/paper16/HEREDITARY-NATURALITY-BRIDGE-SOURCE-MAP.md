# Canonical tuple order/restriction and decoded validity

Source: `sections/decision.tex`, finite natural hereditary domain definition and `lem:finite-lattices`; subordinate to the unchanged full hereditary target, not an alternative carrier.

The three frozen supporting endpoints are:
- TupleLeExact: on actual successfully decoded argument vectors, the actual canonical boolean tuple order is exactly the positional semantic ValuesLE predicate. No caller-supplied tuple membership or order-correctness premise.
- TupleRestrictionExact: on successful original-context decoding, actual reindexing equals `indices` of the literal lower restrictions. The equality includes failure at the destination. No assumption that lower restriction preserves membership is inserted.
- DecodedValid: every retained actual code in a well-formed context decodes to the full semantic Valid predicate, including monotonicity and naturality. This is the first conjunct of frozen DecodeEncode, not the complete target.

Proof route: use original retention to obtain monotonicity and successful natural reindexing. Successful indices plus the checked forward tuple roundtrip identify the exact restricted argument values. Thus no default, lower naturality oracle, extra availability coherence, or changed index convention is introduced. Semantic coding inverse and lattice closure/operations remain separate.

## Planned concrete proof decomposition

- Prove the positional `ValuesLE` cons equation with the actual two list-length invariants derived from successful decoding. Convert attached-prefix zipped `all` to ordinary typed zipped `all`; every component comparison remains the actual global descriptor order.
- Erase only proof attachments in canonical `tupleRestrict`. Prove that zipping the original domains with the componentwise restricted values produces exactly the original typed pairs mapped through the actual lower restriction. Derive the output list length internally. This yields equality with the actual `indices` function, including its rejection cases.
- For a retained code, extract the exact `monotone = true` and `natural = true` conjuncts of EffectiveCarrier. Enumerate real well-formed extensions and full prefixes using already-checked enumeration facts.
- Given typed semantic tuples, obtain actual index tuples from indicesExist and successful reverse decoding. Full-prefix membership follows from the actual canonical bound theorem. Use TupleLeExact to discharge the boolean premise.
- For naturality, the retained boolean predicate must yield an actual successful destination index tuple. TupleRestrictionExact and valuesAfterIndices identify its decoded values with the literal restrictValues result. Never assume an unchanged tuple of indices across contexts. Output existence/membership and the exact successful lookup equations identify both semantic outputs.
- Conclude full Valid from output membership, monotonicity and naturality, then pair with the separately checked code reconstruction in a later fresh exact DecodeEncode gate.
