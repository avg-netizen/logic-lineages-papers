# Reconstructed failed proof sources

These files were reconstructed after independent review found that failed proof sources had not been retained contemporaneously. They are not claimed to be original archived snapshots. Each reconstructed byte sequence matches the complete SHA-256 recorded by its original failed compiler receipt. All three requested versions are recoverable.

Starting source: accepted InternalDivisibilityDifferenceProof.lean, SHA-256 242e8dff7c4e31e551cbd8083cb6bc1c3c0f82267b0d70467e6601bf3b17ca39. This source was read from the permitted working checkout. Prior editing operations are preserved in the worker's current conversation tool-call history; no denied runtime session path was read.

Reverse reconstruction steps, in order:

1. Remove the line `  simp only [addRelabel]` inserted by the recorded sed operation after `rw [onEquality]`. This yields check-04's failed source, hash fe8232b2c7dedc2ee231a7501b90e70404da24c71366bc4393897abc572442dd, matching build-reports/1794005861623954458-6.json.
2. Undo the recorded Python replacement qualifying `congAddRight` as `InternalMultiplicationLawsProof.congAddRight` at the quotient difference application, and remove the inserted line `  change Derivation body Gamma (coprime m (add m a))`. This yields check-03's failed source, hash 2ca23cdad39ef1b242432f28d21328e99f6e727e68a0d669a3adbc0290f9e8e7, matching build-reports/1794005843788735240-6.json.
3. Undo the recorded sed replacement of the word `OTerm` by `OrdinaryArithmetic.Term`. This yields check-02's failed source, hash d80d0f23851408dc2691d847df70043c8ab0bc4d46fbc75d540d422d03bffbee, matching build-reports/1794005833616375849-5.json.

RECONSTRUCTED-FAILED-SOURCES.json maps full paths, complete hashes and receipts. Reconstruction verified each digest before writing the evidence files. The accepted proof and target sources were not changed. No compiler was run for this evidence repair.

The existing chronology caveat remains: target freeze preceded candidate proof writing, but candidate proof writing preceded the first target compilation. Exact reconstruction does not remove that sequencing deviation.
