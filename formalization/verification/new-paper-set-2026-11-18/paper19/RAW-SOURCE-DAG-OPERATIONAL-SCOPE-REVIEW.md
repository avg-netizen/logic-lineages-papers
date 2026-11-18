# Raw source DAG operational development scope review

Approved for parent-controlled bounded LookupProof then EquivalenceProof development, under all six unchanged frozen pins. This is scope approval, not compilation or final correctness acceptance.

Read the actual numeric definitions, typed step/decodeGraph/decode, LookupProof, EquivalenceProof and subsequent EffectiveProof. The numeric checker matches all seven exact-arity constructors, local context prefixes, arrow/case/recursor type equations and backward reference specifications. Lookup bounds are separately checked, so defaults cannot make an invalid index valid. Type coding inverse facts support exact specification injectivity, not a semantic type approximation.

LookupProof retains literal specifications even on invalid tails; decoded_specs uses the actual typed reconstruction converse. EquivalenceProof handles failure propagation separately, then uses successful-tail specification equality and node status. Its final root comparison preserves the empty local prefix and actual root type/index. The proposed result is pointwise check = valid for every raw code, not just encoded inputs.

The subsequent EffectiveProof has the appropriate transport shape: actual checker primitive recursion supplies Computable valid; the checked decode/encode converse reify_exact supplies the literal reifier, including malformed rejection. This later assembly is in scope but requires the operational prerequisites to pass before full acceptance. No general compiler or unfolded-term proxy is credited. No native process was launched by this review.
