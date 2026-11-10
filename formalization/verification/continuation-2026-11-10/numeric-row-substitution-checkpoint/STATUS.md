# Numeric block-row substitution: fresh checked checkpoint

Fresh native verification completed on 10 November 2026 for six exact
supporting contracts: literal entry, row and encoded-row calibration, and
jointly Computable entry, row and encoded-row programs. Every name,
replacement code, signed parameter and occurrence list remains runtime data.
Malformed-payload fallback, zero weights, occurrence order and multiplicity
retain their original definitions. No Primrec strengthening is claimed.

The six-target gate and its namespace audit passed; independent final review
confirmed the complete result and its source correspondence. All 25 owned theorem
and alias declarations have explicit current axiom audits using only
`propext`, `Classical.choice` and `Quot.sound`; one elementary helper uses no
axioms. All 555 local gate dependencies have successful native rows matched
to the frozen source hashes.

This checkpoint adds verification metadata, not mathematical source changes.
The five `BlockRowSubstitutionCode*` source files already exist byte-for-byte
at published baseline `a89b703ffafd70b015aaed43daa3475c7d94b9b2`.
Their exact paths and SHA256 hashes are in `SOURCE-HASHES.json`.

## Current immutable receipt provenance

- `1794302494692422302-44.json`: the first Programs invocation was interrupted
  before its requested target. Only its 410 successful source-matched
  dependency rows were reused. It is not a complete pass or a proof failure.
- `1794303433798105795-44.json`: the authorized unchanged Programs retry
  rechecked the interrupted module, added 141 successful rows and passed
  the requested ProgramsProof with all 14 explicit audits.
- `1794304993879966578-45.json`: fresh calibration passed with two new rows
  and all five explicit audits. Lost earlier local logs were not recovered
  or relied upon.
- `1794305159720606682-45.json`: the exact six-target gate and its
  six-theorem namespace audit passed.
- `1794304229885523131-113.json`: the already-cached Audit module has its
  exact successful source-matched row in this separate current native receipt.

Receipt hashes are listed in `SOURCE-HASHES.json`. This small checkpoint does
not upload raw or older held evidence. Successful checkers were explicitly
waited/reaped, their sessions exited zero, and both shared compiler locks were
verified free at final closeout. No host-wide reap claim is inferred from
isolated process views.

All runs retained the original checker and serialized limits: 2,048 MiB heap,
1,536 MiB RSS, 2,048 MiB minimum free memory, one thread, 90 CPU seconds and
180 wall seconds per compiler. No cold upstream compilation occurred.

Numeric formula/program assembly and original BASE remain pending.
No numbered statement is promoted, and no full-root or remote-CI pass is
claimed. Root imports, register, manuscripts, CI, toolchain and dependencies
are unchanged.
