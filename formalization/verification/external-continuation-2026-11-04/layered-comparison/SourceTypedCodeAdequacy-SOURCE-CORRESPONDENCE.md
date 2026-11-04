# Fixed-context typed source codec adequacy

This is a representation supplier for the paper09 source decision-problem encoding, not a semantic hardness theorem. It uses the unchanged SyntaxCode.Raw, erase, encodeTerm and exact type checker; no new decoder or semantics is introduced.

FixedContextTypeUniqueness says equal erased source trees at the same typed context force equal result types. The exact checker supplies this even where applications erase their internal argument type. Type-code decoding certifies that numerical type equality is actual Ty equality.

TypedCodeInjective says equal numerical encodings of original source terms at the same context and result type imply literal typed-term equality. The proof must account for actual variable indices, application typing, lambda domain codes, and case/rec type annotations. It is not restricted to the generated zero/successor fragment, but still has a fixed context.

GenericControlTransport transports the actual full default-policy assignment for every result type and the existing Scalar/Observation relations for ground terms, every control G, every ordinal valuation and every natural valuation respectively. These conclusions follow from literal syntax equality, not any fixed-Phi interpretation. No control growth, positivity or finite-success premise is assumed, and assignment success or finite denotation is not concluded.

Cross-context transport, coded strict-language definition and many-one semantic reduction remain separate. No manuscript, existing semantics or accepted/frozen source changes; verification-only, no export.
