# Checked: genuine internally bounded CRT for term-defined families

`InternalBoundedCRTProof.actualBoundedCRT` proves the unchanged frozen
`InternalBoundedCRTTargets.ActualBoundedCRT`. The exact alias is
`InternalBoundedCRTStatementChecks.actualBoundedCRTExact`, with actual axiom
closure `[propext, Classical.choice, Quot.sound]` only.

For arbitrary original parameters, any object-language bound n, any term-defined
positive modulus family succ(t(i)), and any term-defined residue family r(i),
triangular coprimality at the distinct indices i<j<n yields one shared code c
satisfying every original congruence below n. The proof uses PA induction on an
object variable, not external finite iteration or semantic Nat reflection.

The successor proof obtains a positive common multiple P of all old moduli
which remains coprime to the new modulus, uses genuine binary CRT, and descends
its congruence through each old divisibility relation. The new divisor helper
eliminates both original existential witnesses genuinely. Existing accepted
sources and literal arithmetic/order/congruence formulas are unchanged.

Target-first compilation passed in `1794004728384652742-10.json`.
Syntax passed in `1794004948978907047-6.json`.
Support, step, induction and exact alias passed in `1794004983678110682-8.json`.
The supplier's receipts and standard-axiom exact alias are preserved under
`congruence-divisor/`. All failed candidates and raw receipts are retained.
The final successful bound was 1,208,548 KiB process-tree RSS, below the unchanged
1,536 MiB cap. No full-root or remote-CI build is claimed.

The frozen definitions and target hashes recheck unchanged. `SOURCE-SHA256.txt`
pins all ten new sources. Independent review accepted all ten sources, both exact aliases, original binder/induction semantics and retained repairs. The coordinator recursively matched821 focused sources against durable successful receipts/logs, with peak1,226,832 KiB across cited receipts. This is not a fresh full rebuild. Publication is handled separately; unrelated prior scratch remains untouched.

This is a supporting internal arithmetic theorem, not the whole sequence-coding
or public-paper result. Formula-defined residue relations are not part of this
frozen target; a separately frozen generalization is feasible by choosing the
new existential residue inside each successor step while preserving old choices.
