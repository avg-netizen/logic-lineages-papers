# Paper 17: actual finite weak-order branch chooses the original maximal signed class

Manuscript: [arithmetic proof](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex), lines 97–114 and 197–220.

- Targets take the literal ordered candidate vector from #1181 and active source labels from #1167. Each candidate's consecutive answer block corresponds to one occurrence against all occurrences. The selected mask marks a block when none of its comparisons is strict less. No caller-supplied maximal key, selected members, consistency oracle or coefficient is used.
- VectorProof derives uniqueness of the exact pair vector from the two actual literal lower-reader hits at every comparison; the candidate is exactly the numeric vector of the one correlated true full-value tape, retaining duplicate ranks and repeated operands.
- FlagsProof shows the selected occurrence mask is exactly membership in the maximum actual full-value class, computed from the literal comparison blocks rather than the maximum's numeric value.
- Proof keeps the original active filtered occurrence order, attaching 2*c for an ordinary field of original signed coefficient c, and c for a genuine long count. The exact maximum exists when the original active label tape is nonempty. The candidate-selected signed sum is exactly the original rowParts doubled coefficient and therefore tests the actual zero class, including negative coefficients and cancellation.
- StatementChecks audits the exact numerical vector, flags, signed original metadata and aggregate aliases.

This is a single-node finite branch selector, not zero replacement, terminal sign, raw primitive recursion, or symbolic closure of every future node.
