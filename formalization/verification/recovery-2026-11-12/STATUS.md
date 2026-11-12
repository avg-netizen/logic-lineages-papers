# Recovery draft: fresh verification required

A cloud workspace reset removed unpublished sources and native build artifacts after checkpoint `9e732bf4`. This isolated recovery branch preserves reconstructed source drafts before further verification. The checked cumulative branch is unchanged.

The previous workspace had passed structural traversal key preservation and initial-minimum absorption gates, but not every file was recoverable byte-for-byte. Those reconstructed files must be checked again; this snapshot does not inherit their lost build results. Lambda native calibration and whole-wrapper lambda introduction remain unverified candidates. No numbered statement is promoted and no full-root or CI pass is claimed.

The original published checkpoints remain preserved. Compiler and dependency pins, accepted mathematical sources and register are unchanged.
