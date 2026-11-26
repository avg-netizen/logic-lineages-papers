# Preservation checkpoint 03, 14 November 11:30 UTC

Pinned Lean 4.32.0-rc1 and matching official Mathlib cache have been restored.
The single fixed-limit combined native preflight is still rebuilding the
inherited local source closure. Its latest observed progress was compiling
InternalLessThanEvaluationProof after InternalEqualityTestEvaluationProof passed.
P12's three owned Fuel preflight modules passed; the Fuel candidate proof has
not yet been compiled. P6's preflight has not yet been reached. No combined
run, new proof, full-root build or CI success is claimed.

The new P6 candidate-decoder design note is preserved as UNPROVED planning,
not an accepted theorem or calibrated implementation. It proposes using original
encode/decode round-trip semantics to expose the candidate decoder; primary-list
enumeration and internal compatibility remain open.

Read-only recovery inventory found89 distinct Lean draft blobs absent from the
current cumulative tree but durably preserved on recovery-drafts-2026-11-12 at
65cd68930901ee72c1d7a284a4618e3f58db9d00. No merge, overwrite or acceptance of
those drafts occurred. The numbered register remains175 checked,2 inherited,
12 pending. Deadline2026-11-15 02:00 UTC remains unchanged.
