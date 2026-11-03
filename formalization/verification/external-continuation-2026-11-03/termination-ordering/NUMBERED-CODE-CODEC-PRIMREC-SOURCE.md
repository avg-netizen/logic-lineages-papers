# Exact recursive-code primitive-recursion corollaries

Paper06 lines551–556 requires effective coded syntax. These are explicitly derived corollaries of the accepted honest Code Primcodable presentation: literal codeNumber and decodeCode are formally primitive recursive for each fixed n. The presentation uses those exact functions, and its primitive encdec requirement was proved from the actual finite success table. No fresh instance, arbitrary coding equivalence or assumed parser effectivity is introduced here.

This small component exposes the usable formal interface, not a new recursive algorithm proof. Existing malformed-input behavior is unchanged. Typed AuxTerm/Arguments/Packed decoding, dynamic binder contexts, full checker effectivity, arithmetic representability and well-foundedness remain separate.
