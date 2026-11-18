# Family coding supporting scope: seven contracts / nineteen pins

Source decision.tex(C) family tables: canonical parameter schema already enumerates all actual head/output/context/base/extra coordinates, including zero arity/empty extras/exhausted ports. Raw vectors fit exactly actual output cardinalities. Lookup rejects absent coordinates and malformed traversals, output rejects out-of-carrier indices. Encoding is optional mapM of actual output carrier indices; failed membership cannot become an output. Decode's [] fallback is off-domain only: CoordinateSuccess and OutputSuccess exclude it for every literal valid coordinate of a fitting code.

EncodingExact gives both validity-to-success/Fits and success/Fits-to-validity, without caller index existence. CodeRoundtrip invokes actual carrier distinctness and schema distinctness; SemanticRoundtrip requires actual membership, not arbitrary off-domain function equality. EncodingCongruence is only valid-coordinate extensionality. Empty schema has literal [[]] raw enumeration and some [] encoding.

These contracts impose no monotonicity/coherence yet and accept arbitrary finite source-head lists. Actual source instantiation continues to use checked SourceCoverage. Full coherent family/lattice, structural interpretation, operator and adequacy are separate. No proof/native before independent exact review.
