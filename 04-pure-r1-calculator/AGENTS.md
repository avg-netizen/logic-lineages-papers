# Working on the pure R1 calculator

Keep this package independently usable: all project source is included here;
there are no imports from private repositories or the larger Alexander thesis
project. Read README.md, FORMALIZATION.md and REUSE.md before changing the proof.
Keep Computer Modern and the explanatory style of the paper.

The actual semantic relation is constructed in Semantics.lean. Correctness.lean
proves its endpoint equivalence through the finite-copy criterion, weighted
forests, concrete copies/obstructions and recursive uniqueness. Preserve the
single-relation language and the distinction from simultaneous order two.
Do not replace the theorem with a definition, semantic class premise or axiom.
No sorry/admit, added axioms or native_decide proofs. State actual coverage.

Python execution and the Lean development have different assurance scopes;
there is no formal Python refinement proof. Preserve the documented coefficient,
marker, induced-map and incomplete-search contracts.

Use scripts/check_lean.py for bounded serialized compilation, or the complete
scripts/verify.py --lean --paper check. The helper caps managed heap, virtual
address space, CPU and wall time. Do not run concurrent compilers, rebuild
upstream dependencies or repeat a cold resource failure. Investigate a changed
cause before a controlled retry. The committed Lake configuration pins public
dependencies; a borrowed local cache is only a development convenience.

The completed lane components are frozen. Root owns integration and Git. Future
agent work must agree ownership before editing shared files; no automatic Git
operations, nested agents or new programme selection from historical notes.
