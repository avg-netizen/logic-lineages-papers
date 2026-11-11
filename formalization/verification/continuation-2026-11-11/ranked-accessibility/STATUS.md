# Native accessibility reflection under substitution

Eight exact native contracts are proved in five Lean modules. Confined numeric successors lift to actual packed terms, positive-path accessibility agrees with original one-step accessibility, and every original GoodSubstitution reflects accessibility of the substituted representative back to the original representative. The original finite symbol set and subtype-closed S are retained.

The proof combines outer induction on transformed accessibility with inner strong induction on original variable count. Genuine positive transformed paths use the outer induction; equality with strict count decrease uses the inner one. Single-bottom substitution is specialized without an added sigma-in-S premise, because GoodSubstitution asks only about variables whose own types lie in the window. Genuine self-edges are retained.

The focused closure contains 743 source-matched modules; exact aliases use only standard axioms or no axioms. Frozen/inherited sources and fixed compiler limits are unchanged. Compact source-first evidence is published; no full-root or remote-CI pass is claimed.

This is native quotient accessibility reflection, not internal scalar-I reflection, converse erasure accessibility or all-type computability weakening. Ordinary native weakening already exists in the repository; this packet gives the stronger arbitrary-substitution reflection route. Final-source/canonical bridges and paper06 lem:id1 remain incomplete. Register: 171 checked, 2 inherited, 16 pending / 189. Stop at 2026-11-11 17:30 UTC without automatic resumption.
