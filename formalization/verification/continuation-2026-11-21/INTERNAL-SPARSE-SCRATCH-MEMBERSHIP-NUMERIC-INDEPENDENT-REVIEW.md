# Recovered Paper 16 numerical scratch membership: scope review

The two restored proof leaves match the historical source SHA-256 values in the recovery author manifest. The frozen all-input comparator uses the literal `scratchMember` program and unchanged `decodeNumbers` on the original numeric pool code, on every input pair; the candidate is not normalized. The check exposes the separately frozen `ExactAllInputScratchMembership` under its fixed alias.

The proof rewrites the actual `listRec` evaluation, uses the fixed equality branch on actual head and candidate, and proves that its ordered fold equals `List.any` by induction on the decoded list. Failure to decode and empty pools both reject; a well-formed occurrence of zero is treated as an ordinary member. It neither takes an externally decoded pool as a premise nor assumes validity of the raw code.

This is not symbolic membership, scratch provenance through parsing, a first-hit index, or a full least/RawMatching claim. The frozen target preflight and the new proof replay are separate checked artifacts. No historical native receipt is admitted, and there is no numbered-statement change.
