# Honest actual recursive-code presentation

Paper06 lines551–556 requires effective coded syntax before arithmetic quotient claims. The Encodable presentation here uses literally the accepted codeNumber and decodeCode, with its existing roundtrip proof. Targets expose the literal encoding calibration, exact encode-after-decode normalization to success ? value+1 : 0, and the actual Nat.Primrec requirement for that normalization. The candidate may construct the corresponding Primcodable instance only after proving this requirement, not assume it before the comparator.

Accepted code-decoder success effectivity and successful-decode numeric soundness pay the requirement. No arbitrary coding equivalence, membership oracle or omitted malformed-input cases are used. No accepted definitions are changed.

This presentation is for untyped recursive Code(Fin n), for each fixed n. Actual typed Packed decoding, context reconstruction, the whole checker, arithmetic representability and well-foundedness remain separate.
