# Original recursive guard constructor equivalence

Frozen exact1, no proof authored. Dependency OriginalCodeValidityCoherence FULL01 passed receipt 1794749031662337425-6; final independent acceptance is pending at freeze time. Existing passed sources are untouched.

## Literal correspondence
The check is the unchanged OriginalCodeValidityGuard.check, calibrated to original decodeCode including its roundtrip filter. Its table is exactly tableProgram n [raw+1,raw], and final lookup is at raw. The new allowed formula retains exactly the association and ordered six clauses of OriginalCodeDecoderStep.Targets.allowed. The ONLY semantic substitution is that each active child lookup into the previous parent table becomes the actual graph of that same unchanged recursive check on the child at [child+1,child].

Tag 0/3: true; tag 1: first child; tag 2/7: both children; tag 4: original head check and first child; tag 5: original head check and both children; tag 6: payload zero. All other tags are rejected. Original total type/type-list decoding permits no extra restriction. Original unary firstOf/secondOf and the already checked headOf are actual field observations, not assumed typed constructors or head validity. Parent raw pairing and all four observations are quantified internally in the source calculus over arbitrary contexts/body, with no native table image premise.

## Constructive proof plan
1. Introduce actual tables at (fuel raw,bound raw) and (fuel raw+1,bound raw) by original program graph totality. Recover nextRow from the recurrence, then use actual bounded row lookup intro/elimination to identify parent acceptance with codeNext acceptance on the preceding table.
2. For active tag1/4 derive first<raw internally; for active tag2/5/7 derive both children<raw from the original arity/selector theorems and raw tag evidence. No public strict-descent premise. No impossible small-raw constructor assumption: the same internal descent argument handles those cases.
3. For each active child introduce its actual own table (child+1,child). Prove child<raw (preceding parent fuel), child<=raw (parent bound), child<child+1 and child<=child. Invoke accepted sufficient-fuel coherence on these actual table graph outputs, in either direction. Unfold the literal check graph to transport accepted lookup iff own-cutoff guard acceptance.
4. Transport each ordered clause in both directions and apply the original codeNext branch equivalence. Nonrecursive tags use no spurious child premise. Reconstruct parent check using its actual full table and final lookup. All internal witnesses are eliminated via original query cases, not supplied at the endpoint.

## Limits
This is genuine recursive guard constructor semantics, not supplier installation. It does not identify raw code numbers with generic Encodable node numbers, prove default[] dependency conversion, or complete original source E/computability. No AST is changed, no unknown tag added, no output-other-than-one equivalence asserted. Native calibration is not reflected into internal derivations.
