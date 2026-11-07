# Positive common multiple existence

Accepted exact theorem `InternalBetaModulusCoprimalityExistenceStatementChecks.actualPositiveMultipleExistsExact` inhabits the unchanged frozen `InternalBetaModulusCoprimalityTargets.ActualPositiveMultipleExists`.

The proof specializes the accepted object-calculus common multiple induction to fixed one and the identity index family, supplies coprimality using contextual symmetry of `coprimeOne`, and projects away coprimality under the existential. Generic contextual `coprimeSymmetry` is also available to consumers. Both declarations audit to only `propext`, `Classical.choice`, and `Quot.sound`.

Successful bounded receipt: `build-reports/1794006028146577950-9.json`, copied in `attempt04/`. Peak observed process-tree RSS: 1,192,380 KiB. The unchanged 2048 MiB heap / 1536 MiB RSS / 2048 MiB minimum-free, serialized checker command was used. Compiler slot released after success.

Attempts 01–03 preserve the failed sources, logs and receipts. Attempt 04 preserves accepted sources, log and receipt. `SHA256.json` pins these artifacts and both live source files. No accepted existing source or frozen target changed. No Nat semantics, admission, added axiom, native decision shortcut, commit or publication was used.

This supplies positive common multiples internally. It does not by itself establish beta modulus pairwise coprimality, CRT assembly, or the complete beta witness consumer.
