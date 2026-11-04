# Type-indexed syntax carrier effectivity and ordinary arithmetic

Paper 06, lines 572–581, conjoins typedness in C_tau clauses. This component formalizes only the type-indexed syntax carrier, not C_tau, I, inductive definitions, or ID1 proofs.

Actual typedCanonicalCarrierTest is retained verbatim. The numeric wrapper uses the exact frozen OrdinaryArithmeticQuotient.Context decoder and accepted NumberedNumericDecoding.decodeType. The type codec is total on Nat by the already checked type grammar bijection; there is no invented invalid-type rejection. Context or term decoding failures reject according to the actual implementations.

Primitive recursion is fixed per n/arity/Gamma, jointly varying symbols, type window, requested type, and numeric term. The ordinary first-order arithmetic formula has Context code/type code/value free variables. Concrete semantic calibration requires subtype closure and actual confined Packed witnesses of the requested type. No C_tau computability predicate, accessibility or well-foundedness is inferred.
