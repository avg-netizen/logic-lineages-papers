# Exact original multiplicity counter (exact4)

NumberedExchangeGuardsPrimrecProof.countPrimitive folds right with if b=a then total+1 else total. permutationPrimitive compares these counts for all entries in source++target. This packet implements precisely that fold using actual equalityTest, successor and raw list recursion, not a sorting substitute.

NativeCount asserts actual numeric List.count, and actual original typed (Ty×Code) count after generic encoding. The latter must use Encodable injectivity, preserving both type and term plus multiplicities. Internal nil/equal-cons/unequal-cons laws consume actual cons and recursive-tail count graphs plus an actual internal equality/negation. They prove actual program graphs without semantic reflection or failed-proof-search inference.

This is a direct count-based permutation prerequisite, not the whole permutation checker. Full permutation quantification, internal extracted-spine correctness, window/sourceHeads and headMove/E/source stability remain open. Existing graph/extraction is native-calibrated only; no tuple mutation.
