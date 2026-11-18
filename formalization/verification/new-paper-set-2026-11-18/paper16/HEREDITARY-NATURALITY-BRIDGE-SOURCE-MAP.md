# Canonical tuple order/restriction and decoded validity

Source: `sections/decision.tex`, finite natural hereditary domain definition and `lem:finite-lattices`; subordinate to the unchanged full hereditary target, not an alternative carrier.

The three frozen supporting endpoints are:
- TupleLeExact: on actual successfully decoded argument vectors, the actual canonical boolean tuple order is exactly the positional semantic ValuesLE predicate. No caller-supplied tuple membership or order-correctness premise.
- TupleRestrictionExact: on successful original-context decoding, actual reindexing equals `indices` of the literal lower restrictions. The equality includes failure at the destination. No assumption that lower restriction preserves membership is inserted.
- DecodedValid: every retained actual code in a well-formed context decodes to the full semantic Valid predicate, including monotonicity and naturality. This is the first conjunct of frozen DecodeEncode, not the complete target.

Proof route: use original retention to obtain monotonicity and successful natural reindexing. Successful indices plus the checked forward tuple roundtrip identify the exact restricted argument values. Thus no default, lower naturality oracle, extra availability coherence, or changed index convention is introduced. Semantic coding inverse and lattice closure/operations remain separate.
