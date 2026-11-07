# Original beta witness bridge: checked supporting component

The original betaFormula now has an exact internal two-witness matrix bridge.
Bound variable 0 remains the quotient and bound variable 1 the strict-bound
witness. No pairing encoding, beta predicate symbol or alternative graph is
introduced. The existing calculus now has admissible introduction and
fresh-variable elimination rules for exactly that formula.

An additional empty-context theorem proves betaFormula 0 b i 0 for arbitrary
ordinary terms b and i and arbitrary positive body. Its explicit witnesses
are quotient 0 and strict-bound witness (i+1)*b. This is a zero-code instance,
not totality or uniqueness for arbitrary first code components.

Four frozen exact aliases compile using only propext, Classical.choice and
Quot.sound. The complete focused closure has 744 source-matched modules.
Existing arithmetic and finite-block evidence is inherited by exact hash.
The bounded checker used one thread, 2,048 MiB heap, 1,536 MiB RSS and
2,048 MiB minimum free memory; inherited/current peak is 1,226,832 KiB.
Three failed syntax candidates and their native receipts are preserved.
The repairs only correct binder API selection and substitution proofs;
frozen definitions, targets and original semantics are unchanged.

General division/remainder existence and uniqueness, beta totality and
uniqueness, finite sequence coding and general primitive recursion remain
open, as do C_tau closure, accessibility and whole internal ID1. II5 is
excluded. Register unchanged: 167 checked, 2 inherited, 20 pending.
No full-root build, remote CI pass, merge or existing-source change claimed.

Independent read-only review accepted frozen hashes, original binder order,
freshness conditions, exact aliases and all failed-candidate snapshots.
Source-closure receipt matching was verified separately by the author.
