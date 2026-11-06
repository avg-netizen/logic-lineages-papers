# Checked beta modulus coprimality and positive common multiples

All three frozen exact targets passed, with only propext, Classical.choice and Quot.sound:

- ActualDifferenceCoprimality: (w+1)|(b+1) implies coprime(M_i,M_(i+w+1)), where M_i is the unchanged InternalBetaWitness.modulus(b+1,i).
- ActualBetaModulusPairwise: the literal bounded universal that every x<n satisfies (x+1)|(b+1) implies the original InternalBoundedCRT.pairwiseBelow for exactly those beta moduli. No coprimality premise remains.
- ActualPositiveMultipleExists: for every arbitrary object bound n, an actual positive common multiple exists internally.

Final exact gate: native/1794006144529865604-7.json. Definitions/target-first pass: native/1794005904476849715-5.json. Existence and coprimality symmetry have their focused exact gate in existence/ (receipt 1794006028146577950-9.json). The separately checked difference supplier is under ../difference/.

The arithmetic proof derives coprimality with b and with each positive divisor d using literal certificates. Product coprimality yields coprime(M_i,d*b); checked divisibility-difference gives coprime(M_i,M_i+d*b). An explicit internal arithmetic identity identifies the latter sum with the original later modulus. The bounded proof eliminates i<j to obtain its positive gap, derives that the gap predecessor is below n, instantiates the original bounded divisibility hypothesis, and introduces both actual object universals in the CRT's required orientation.

Positive common multiple existence specializes the already accepted object-induction common-multiple theorem to the unit and the identity family. No semantic Nat reasoning, external finite-length induction, unproved product existence, hidden choice sequence or new axiom is used.

All failed proof candidates and corresponding native receipts are retained. Repairs added missing namespace opens and explicit normalization of the nested free-variable renamings. Frozen definitions, target and correspondence hashes remain unchanged. No existing accepted source was modified. Publication is handled separately. Independent review accepted all ten new sources, literal target scopes, aliases and final receipts. The coordinator recursively matched818 focused sources to durable successful receipt/log paths, peak1,226,832 KiB across cited receipts. Three failed difference drafts were reconstructed with exact hashes matching original failure receipts, explicitly labeled as reconstructions. The difference target was frozen before proof writing but first compiler-preflighted after candidate writing; this chronology deviation is retained in difference/STATUS.md, and the namespace-only correction did not alter its mathematical formula.

Scope: genuine internal beta-modulus prerequisites only. This does not yet combine relational CRT with bounded residues, supply arbitrary residue bounds, prove full sequence coding, or close a whole-paper theorem. The sole compiler slot was released to the coordinator after the successful exact gate.
