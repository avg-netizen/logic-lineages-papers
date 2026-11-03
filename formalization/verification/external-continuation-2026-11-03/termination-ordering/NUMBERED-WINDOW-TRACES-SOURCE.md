# Confined numbered traces and contexts

Source: paper06 lines 536–556 and 625–660 use actual numbered steps with zero-cost primary equivalence, finite full-tuple simulations and a positive raw-step count for strict comparisons.

The new packed, typed and tuple traces use exactly accepted WindowStep/WindowArgumentStep and WindowPrimary/WindowArgumentPrimary. Raw edges contribute one, primary motion contributes zero, and composition adds counts. Erasure preserves the literal count. Packed-to-typed presentation uses actual type preservation of the erased original trace, not a supplied intermediate type invariant.

Boundary and TupleBoundary are explicit occurrence relations with start, finish and either child of composition. All-boundary confinement quantifies over every such witness, including every intermediate composition junction. No confinement is a trace constructor premise. The proof derives it from actual initial confinement and the accepted primitive/equivalence preservation theorems.

The context interfaces lift lambda bodies, function-side auxiliary application, actual tuple head/tail composition, ordinary bases and numbered bases/extras. No positive auxiliary-application argument lift exists; primary argument congruence remains zero-cost.

These eleven targets establish actual restricted paths and context suppliers. They do not identify any existing unrestricted simulation certificate with a restricted one, prove finite quotient classes or computable representatives, or complete arithmetic simulation/accessibility. The exact original-spine and five-way derivation constructions must later supply restricted paths. Root reviewed the exact scoped interfaces before candidate authoring.
