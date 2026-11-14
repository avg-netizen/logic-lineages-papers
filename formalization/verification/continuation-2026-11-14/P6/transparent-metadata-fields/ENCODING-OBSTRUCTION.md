# Real source encoding mismatch, not a proof elaboration repair

Frozen metadata NativeMetadata requires generic Encodable encodings for head and type-list fields, matching original ExchangeLayer.input. The frozen AST extracts literal headNumber/typesNumber from codeNumber payloads. These are not definitionally equal; for heads they are genuinely different.

NumberedHeadCodecPrimrecDefinitions.headEquiv encodes HeadCode.cases Ty.ground as Sum.inr (Sum.inl Ty.ground). Mathlib Encodable.encode_inl/encode_inr and type encoding give 1. Original headNumber (.cases .ground) is Nat.pair 2 0, i.e. 6. Thus the raw head selector cannot satisfy the original NativeMetadata target on an ordinary node with this head.

Internal constructor graph claims remain correct for raw numeric metadata and have passed receipt1794678865148514648-5. They do NOT establish native calibration to the encoded semantic field supplier. Native candidate01 failed1794678905673760061-5; exact source/manifest/full receipt/log preserved. No frozen statement or AST edited; no retry claiming mere proof-only repair.

A faithful installed supplier needs an explicit raw-head-number to generic-Encodable-head conversion (and separate type-list encoding conversion). Its internal conclusion must describe that actual conversion graph, not equate encoded outputs to raw metadata. This requires a newly reviewed source-corrected specification rather than weakening or silently changing this frozen packet.

## Source refinement after inspecting Mathlib list encoding

Mathlib/Logic/Equiv/List.lean:44–64 defines encodeList []=0 and encodeList(a::l)=Nat.succ(Nat.pair(encode a)(encodeList l)). Thus typesNumber and generic Encodable encoding of List Ty are extensionally equal by induction, since Ty encoding is typeNumber. The earlier wording suggesting a separate type-list conversion algorithm was too broad: an explicit equality proof is needed, but no new list algorithm. The genuine head mismatch remains unchanged. Original note retained byte-exact at failed/native01/ENCODING-OBSTRUCTION-original.md.
