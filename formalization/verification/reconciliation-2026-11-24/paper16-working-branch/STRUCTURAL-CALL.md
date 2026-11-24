# Paper 16: simultaneous substitution of source and whole argument tuple

A fresh pinned Lean check verifies `exact_FixedSimultaneousFreeAllCall`.
It compares the original-spine call on the source and all original
argument codes in the same actual free-image environment with
`concreteOutput` of `apply` after simultaneously substituting both
the source and the typed tuple. This covers both empty and nonempty
tuples, retains the operator fixed point, and makes the source and
resulting coverage premises explicit.

The nonempty case reuses the five exact source blobs from the older
proof branch. Its old acceptance 1488 is branch-local, not the
different 1488 already present in the newer live register. The empty
case uses value agreement and encoding congruence, not a nonempty
prefix or currying equation. The fresh receipt and named axiom logs
are pinned in the adjacent JSON and ZIP.

This strengthens the support for the current Paper 16 structural
interpretation lemma (decision.tex 149 onward), but does not promote
it. Explicit coverage, the empty bound context, and exact overall
substitution/interpretation conjunction correspondence are still
separate. The numbered register remains 160 checked / 7 pending.
No manuscript, toolchain, manifest, CI workflow or resource limit
is changed by this proof checkpoint.
