# Semantic blocker: false native target, not a completed packet

OriginalNumberedEnumerationBranch.Targets.NativeBranch is false for its frozen AST. Do not repair it by changing targets, encodings, or lists silently; do not accept this packet. The raw internal helper still has useful independently compiled proof sources.

Exact mismatch: NumberedHeadCodecPrimrec.headPrimcodable uses headEquiv into Bool ⊕ (Ty ⊕ (Ty ⊕ ((Ty × Ty) ⊕ Fin n))). Thus Encodable.encode (HeadCode.cases Ty.ground) = 1, while NumberedLeastCodeRepresentative.headNumber (HeadCode.cases Ty.ground) = Nat.pair 2 0 = 6. The branch inserts input head fields verbatim into codeNumber tag5 payloads, so the actual encoded-head list cannot be used without conversion. A scalar equality assumed in NativeProof.numberedEncoding is false. Both failed native snapshots retained; no successful endpoint claimed.

TypeLists packet remains accepted and unaffected. Numbered Row01/CrossBinding01/Cross01 independently COMPILE_PASS 1794772238417207421-6, standard audits, proving actual raw row/cross membership introduction only. Frozen three files and all current proof drafts/manifests/receipt retained in semantic-blocker/PRESERVATION.json. The actual opposite-direction OriginalHeadEncodingBridge.encodeHead cannot be substituted for the missing conversion.

Next work: separate explicitly frozen original Encodable HeadCode→headNumber converter with deliberate invalid-default0 semantics, exact actual decoder native calibration and internal inverse-on-valid-source graph contract. Only after acceptance can a distinct corrected branch packet map that converter over heads before the cross product, retaining typed target and revising internal observation contract explicitly. Full enumerate/Q remains unpaid.
