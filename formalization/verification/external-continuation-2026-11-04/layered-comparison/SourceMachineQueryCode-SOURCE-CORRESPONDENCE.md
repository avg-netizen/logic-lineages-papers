# Scalar source-query packaging

This is an encoding supplier for the paper09 hardness.tex lines 294–319 construction, not yet a semantic decision-language reduction. It preserves the exact existing source codec and standard Encodable/Primcodable tuple representation.

The scalar output packs a triple (n,R,L), where n=4+the actual compiled witness count and the numeric aggregate is originally (L,R). The reversal is deliberate: the strict comparison is R<L. ExactPackaging proves the standard triple encode/decode roundtrip and identifies generated requests with the actual compiled context length and literal aggregate source encodings.

GeneratedSourceValidity uses the existing SyntaxCode.check, with a context of n ground type codes, to verify both generated source terms at ground type. It must use the accepted all-ground context theorem and exact compiler length, rather than assuming any raw list is well typed. This is validity only for the generated outputs, not every natural package.

UniformPrimitiveRecursive covers tuple packing/unpacking and the request/output maps, using standard Primcodable products and already proved uniform numeric compilation. It does not assert a Gamma coded strict-language semantics, representation independence, typed erase injectivity, or a many-one reduction theorem. The existing fixed-Phi Universal/forward compiler is not identified with Gamma semantics. Complexity, runtime, weak comparison and full source hardness/completeness remain separate.

All accepted/frozen sources remain unchanged; verification-only, no export.
