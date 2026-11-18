# Independent final review: raw derived composition (root, local continuation)

Accepted as a supporting four-contract endpoint. Reviewer: root of the local
three-party continuation (not the lane B author). No reviewer native run.

All eight frozen pins recomputed and match. The Definitions, Targets and
StatementChecks files are byte-identical to the pre-proof remote checkpoint
ff2e5a5b8 (`git diff` empty), so the comparator approved in
RAW-DERIVED-COMPOSITION-PRE-SCOPE-REVIEW.md is the one that was proved; only
the Typed, Success, Counts and Primitive proof files changed. Compiler-free
recursive evidence was reproduced independently and is JSON-identical to the
author's file: 156 source-matched modules, zero errors, four exact aliases
depending only on propext, Classical.choice and Quot.sound. Dedicated gate
receipt 1795032077282946769-40; proof receipt 1795031951097795584-52. The
proof and definition files contain no unsafe, opaque, implemented_by, extern,
partial, axiom, sorry or native_decide.

The local verifier differs from paper19/verify_packet.py only in resolving
package symlinks before joining the search path and in accepting the Elan
selector with the pinned toolchain prefix, which is how scripts/check.py
itself fingerprints the compiler on this host.

Scope is exactly the frozen comparator: detectors, right-fold aggregate and
upper/lower wrappers on the shared-DAG codec, with typed exactness, arbitrary
raw-success reconstruction, rejection and counts, and joint Computable checked
routines. No numbered statement is promoted; thm:compiler still needs the full
effective input/Plan compiler. Five failed editions are preserved under
paper19/raw-derived-composition-failed/.
