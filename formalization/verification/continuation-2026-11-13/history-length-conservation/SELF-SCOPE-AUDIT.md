# HistoryLengthConservation accepted scope

Full exact2 passed receipt 1794589028195610266-17 with standard-only axiom audits. All Lean source bytes are immutable.

For arbitrary symbolic certificate, initial history, output history, common index and common fuel, an actual literal-kernel full run at the original encoded certificate bound ending in SOME output with drained lines implies true length(output) = true length(initial history) + true length(certificate). Empty initial history yields exactly length(output) = length(certificate).

The proof first establishes a true-length invariant simultaneously covering NONE rejection and SOME conservation. Each successful actual cons transition adds exactly one actual entry; the selected NONE branch cannot recover to success. Raw certificate cases use internal pair surjectivity and true-length induction. Actual bound conversion transfers the result to the original encoded bound. There is no native evaluation reflection, image/validity premise, or assumed length equality.

This pays the original MP antecedent-length versus output-history-length mismatch. It does not itself install standalone length at the current SAME root, construct the trailing MP certificate, pay its validity leaf, or prove HB2/HB3. The separate repository-root VALIDITY-GAP-AUDIT.md was read and agrees: native validity calibration cannot supply symbolic acceptance of a newly encoded line.
