# Bounded coprime common multiples: checked supporting theorem

`InternalCoprimeMultipleStatementChecks.actualBoundedCoprimeMultipleExact` has the exact frozen type `InternalCoprimeMultipleTargets.ActualBoundedCoprimeMultiple`.

For arbitrary object terms m and n and arbitrary term t with one distinguished index variable, the object calculus proves:

- If each positive modulus succ(t(i)) for i<n is coprime to succ(m), then there exists a positive P coprime to succ(m) divisible by each of those moduli.
- Coprimality is the existing formula saying that every positive common divisor is one.
- Positivity of P is expressed by existentially quantifying its predecessor p and setting P=succ(p).
- The bound n is an arbitrary object term. The proof invokes `natInduction` on a formula with a fresh object variable, rather than metatheoretic finite-length induction.

The successor case uses actual product coprimality, divisibility under multiplication, positive-product normalization, bounded-universal successor splitting, and fresh existential transport. The empty family uses P=1. All original parameter variables are preserved by the explicit renaming/substitution lemmas.

## Verification

Exact alias and proof pass: `build-reports/1794004267197609210-7.json`, log `induction-05.log`. Actual alias axiom closure: only `propext`, `Classical.choice`, and `Quot.sound`. Peak process-tree RSS in this final invocation: 1,203,448 KiB, below unchanged 1,536 MiB cap. Heap 2,048 MiB, minimum free 2,048 MiB, one thread, existing CPU/wall caps unchanged.

Supporting successful receipts:

- Frozen definitions and targets: `1794003651440043699-5.json`.
- Substitution/renaming syntax: `1794003993877650064-7.json`.
- Bounded zero, elimination, restriction, successor extension, and mapping: `1794004022829475407-7.json`.
- Common-multiple introduction/elimination and equality transport, plus base: `1794004108892070357-7.json`.
- Successor construction: `1794004165448279559-7.json`.

Source hashes are in `SOURCE-SHA256.txt`; original target hashes in `TARGET-SHA256.txt` remain unchanged. All failed source candidates and logs are retained here. One induction candidate reached the default heartbeat bound; its proof structure was refactored with an explicit successor-instance equality and opaque local contexts. No resource limits were raised.

## Boundaries

This is a common-multiple supplier for bounded-family CRT, not bounded-family CRT itself, a beta-code append theorem, or the entire paper. The family is arbitrary within the frozen term-defined positive family t(i) syntax; no claim is made here about arbitrary graph-defined functions. Independent read-only review accepted all twelve new sources and exact aliases, frozen provenance, binder/induction semantics and failed repairs. The coordinator recursively matched809 focused sources to durable successful receipts/logs. Peak across all cited successful receipts is1,226,832 KiB. This is not a fresh full dependency rebuild. No full-root or remote-CI build is claimed. No accepted preexisting source was edited. Publication is handled separately by the coordinator.
