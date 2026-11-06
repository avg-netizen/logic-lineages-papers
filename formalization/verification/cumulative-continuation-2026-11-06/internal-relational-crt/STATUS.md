# Checked: internally bounded CRT for arbitrary residue relations

`InternalRelationalCRTProof.actualRelationalCRT` proves the unchanged frozen
`InternalRelationalCRTTargets.ActualRelationalCRT`. The exact alias is
`InternalRelationalCRTStatementChecks.actualRelationalCRTExact`, whose actual
axiom closure is `[propext, Classical.choice, Quot.sound]` only.

For any object bound n, term-defined positive modulus family succ(t(i)), and
arbitrary relation formula R(i,r) in the existing expanded language (including every ordinary arithmetic relation), triangular modulus coprimality and
bounded availability `forall i<n, exists r, R(i,r)` imply one shared code c with
`forall i<n, exists r, R(i,r) and congruent(c,r,succ(t(i)))`.
There is no functionality premise or supplied choice sequence. All original
parameters, literal congruence/order/coprime formulas, and internal quantifier
scopes are preserved. PA induction uses the fresh object variable. Each new
residue is chosen by the original existential elimination rule; preservation
transports old witnesses without replacing R or choosing an external sequence.

The separately accepted term-defined CRT and all earlier sources are immutable;
its ten-file hash manifest was rechecked successfully after this work.
The new definitions and target remain exactly as frozen before proof authoring.
`SOURCE-SHA256.txt` pins the eight new files. No source uses admissions, new
axioms, semantic Nat reflection, or certificate-only premise substitution.

Target-first passed: `1794005077473632825-10.json`.
Choice helper passed: `1794005210324965465-8.json` (raw evidence under `choice/`).
Syntax and support passed: `1794005327711103495-7.json`.
Step, induction and exact alias passed: `1794005365871972992-17.json`.
The failed syntax and two failed step candidates and all raw receipts are kept.
Peak successful observed process-tree RSS was 1,205,900 KiB, under the unchanged
1,536 MiB cap. Compiler runs were serialized with the 2,048 MiB heap and minimum
free-memory limits. No full-root or remote-CI build is claimed.

The compiler is idle and the sole slot is released to the coordinator. Independent read-only review accepted all eight sources, exact target/alias, binder and induction semantics, receipts and repairs. The coordinator recursively matched828 focused sources to durable successful receipts/logs, with peak1,226,832 KiB across cited receipts. This is not a fresh full rebuild. Publication is handled separately. The unrelated prior product-coprimality scratch was untouched.

This theorem is a supporting internal arithmetic/coding supplier. It does not
itself prove suitable beta-modulus pairwise coprimality, full finite-sequence
coding, or a whole public-paper theorem.
