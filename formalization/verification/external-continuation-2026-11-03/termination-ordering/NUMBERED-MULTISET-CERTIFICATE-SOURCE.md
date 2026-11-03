# Occurrence-preserving primitive multiset certificates

The original PrimitiveMultiset relation is used unchanged. A concrete certificate supplies kept, removed and inserted lists, with exact source/target permutations and nonempty removed. The checker retains duplicates and list positions. For each inserted occurrence it requires one pair consisting of an index into the removed list and an actual finiteMark label. The recursive checker rejects missing or extra witnesses and out-of-range indices. A removed index may be reused for multiple inserted occurrences, exactly as the original generalized multiset rule permits. No cancellation or one-to-one matching is imposed.

The four targets prove exact replacement certificate existence, witness-list length equality, exact equivalence to PrimitiveMultiset, and target confinement derived from source confinement using actual mark preservation. No subtype closure or head precedence premise is needed for this primitive list relation. The certificate is typed executable data, not yet a natural-number decoder or an arithmetic representation. Its later use in Mul still requires the actual numbered source, head guards, typed target base and the original constructor.

No full WindowStep decision, quotient accessibility, arithmetic definability or unrestricted local transitivity is claimed.
