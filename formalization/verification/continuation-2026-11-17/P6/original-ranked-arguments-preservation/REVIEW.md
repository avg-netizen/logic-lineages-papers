# Independent review: hold / revise

Do not freeze this comparator as an approved preservation obligation. All three proposed hashes match, but a raw-domain mismatch remains. No compiler was run and this is not a kernel-verified counterexample or accepted refutation.

## Guard discrepancy

OriginalUniverseDecoder.argumentsCheck genuinely retains the typed transition and raw+1 fuel, including all M/W guards. OriginalTypedDecoder.nilStep requires BOTH payload=0 and expected type-list=0. However OriginalArgumentPermutation.check only requires two successful entries extractions and count comparison. ArgumentEntriesLayer.step returns the constant 1 (Some empty entries) for EVERY raw tag6, without checking its payload. ArgumentEntriesRecursor.RawProof.rawValueEquation and stepIgnoresTail make clear that the selected raw recursor does not restore a missing nil-payload check. The non-cons tag6 layer ignores tail answers. Thus the assertion in the provenance that source entry facts and permutation suffice to reconstruct the original target spine is unsupported.

A precise diagnostic candidate is count=types=0, base=pair(6,0), target=pair(6,1), arbitrary Gamma/context and fixed M/W. The base is canonical argumentsNil; the target has the same nil tag but invalid nonzero payload. Both entry extractions yield the empty list, so their multiplicities agree. The source arguments checker can finish its empty-argument request without any term M/W checks; the target nilStep rejects its payload immediately. Additional raw+1 fuel cannot turn a failed state into success. This candidate uses the original ASTs, not a weakened evaluator. It is source analysis only, not a compiled arithmetic refutation.

Homogeneous ground annotations solve the positional-type issue but do not repair malformed raw spine termination. The same omission can occur at the terminal nil of a nonempty target spine. The earlier withdrawn zero/succ diagnostic and application-entry swap are separate issues and are not being asserted here.

## Required revision boundary

Preserve this proposal and diagnostic. A successor must explicitly retain sufficient original raw syntax validity of the target argument spine, or prove that validity from an independently justified source-level restriction. Do not add target argumentsCheck success or any equivalently strong typed-success premise. Do not silently strengthen the original permutation AST or claim that its two Option gates establish canonical nil payloads. Any new shape premise must be reviewed as a narrower meaningful original-source transport obligation, with provenance admitting the restriction, rather than pretending to prove the current arbitrary-raw endpoint.

The current raw+1 bound and guards must remain unchanged. Arbitrary fixed M/W are not the issue: complete-entry permutation preserves each child term and its local context, but valid canonical target syntax and bounded reconstruction still require real proof. HeadMove-to-same-count and full source preservation remain unpaid.

Only this review and the observed-pin record were written. No targets, proofs, checker, or frozen files were changed. No native check or proof was authored.

## Follow-up: whole extraction and original caller domain

Inspection of ArgumentEntriesRecursor.Proof.originalExtraction confirms the selected recursor uses the generic nativeFinalValue theorem on rawValue/layerCoherence, only afterwards specializing to codeNumber. RawProof.rawValueEquation reduces a tag6 raw node to the constant Some-empty step regardless of payload. Both outer Option gates in OriginalArgumentPermutation.check therefore succeed for the diagnostic pair; their predecessors are zero, so the comparison is the empty/empty append/count fold with base truth 1. There is no later payload guard in this graph. This is inspection of source and existing theorem interfaces, not an executed native computation.

A source-supported narrower domain exists: NumberedExchangeCode.argumentPermutation is originally defined over Code (Fin n), and OriginalArgumentPermutation.NativeProof.nativeOriginal calibrates exactly base,target : Code (Fin n), encoded by codeNumber. OriginalRawSyntaxTransport.nilConstructor is literally pair(6,0); the source Code domain cannot produce the malformed nil candidate. A new explicitly source-Code-domain comparator could retain arbitrary untyped target Code, without assuming target typed success, and still require an internal derivation. It must openly abandon this proposal's arbitrary-raw scope and obtain fresh review; native calibration is not a license to reflect semantic truth into the internal calculus.

The source ordinaryNeighbors uses argumentsFromList to build typed Arguments and classCandidates filters by decodePacked. Those facts explain why the source caller excludes malformed outputs but should not be turned into a circular desired-target-typing premise. No ready independent untyped arithmetic spine validator was established by this review. If an actual canonical-spine construction lemma is chosen instead, its source correspondence and absence of typing assumptions require separate review. Current unrestricted raw preservation remains parked.
