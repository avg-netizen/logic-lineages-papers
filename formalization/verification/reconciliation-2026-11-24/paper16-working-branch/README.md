# Paper 16 working-branch verification

Development is on the single reconciled branch in draft PR #12. Whole-
repository CI and the focused Paper 16 checks are separate: the former
currently stops at the legacy `ModelsAlgebra.Differential.FiniteExtension`
resident-memory limit even when the focused proofs pass. The branch does
not change this limit, and the evidence below is not a full CI pass.

## Where to start

* [Structural calls](CONCRETE-STRUCTURE-AND-UNION-BOUNDARIES.md) and
  [literal installation](LITERAL-PRESENTATION-INSTALLATION.md): concrete
  binder prefixes and capture-avoiding named substitutions, with a finite
  code environment generated from the actual map.
* [Selected address transport](ALL-RANK-ADDRESS-TRANSPORT.md): all target
  ranks. The literal installation checkpoint also includes wrappers for
  the ordinary positive-address program without requiring rank filtering.
* [Ordered split refutation](LITERAL-ORDERED-SPLIT-REFUTATION.md): why
  the original certified split uses permutation, not ordered equality.
* [J characterization](LITERAL-J-CHARACTERIZATION.md): exact raw carrier
  and scalar-members criterion for J in the chosen endpoint-guarded
  presentation. The scalar uniform all-terms theorem remains open.
* [Direct hops and root classification](SCALAR-PATH-AND-ROOT-CLASSIFICATION.md):
  a positive path's actual first hop, the eight typed root cases, and
  the conditional neutral/fresh work on the scalar side.
* [Literal context descent and fuel](LITERAL-CONTEXT-OWN-FUEL.md):
  exact numerical own-fuel equivalence and open function-context peeling.
* [Open auxiliary own-fuel induction](AUXILIARY-OWN-FUEL-INDUCTION.md):
  an actually descending fallback and original strong induction give
  the open child's own-code graph in the selected typed checker.
* [Typed auxiliary children](AUXILIARY-TYPED-CHILD.md): the actual
  same-context strict memo recovers both original child guards, giving
  the same typed callback on the child's own witness.
* [Actual child addresses and target carriers](ADDRESSED-AUXILIARY-AND-CARRIERS.md):
  actual reported auxiliary least addresses and direct hops; a separate
  ordinary installation gives a scalar carrier at each direct edge's target.
* [Covered carriers and remaining neutral rules](COVERED-CARRIER-NEUTRAL-BRIDGE.md):
  one covered selection and its carrier wrapper; actual trace recovery
  and child installation with its explicit destination scalar check.

## Rerun the focused work

With the repository's pinned Lean toolchain and Mathlib objects
available, from `formalization/` run:

```sh
python3 scripts/check.py --timeout 180 --cpu-seconds 90 --memory-mib 2048 \
  --rss-mib 1536 --min-free-mib 2048 --threads 1 \
  LogicLineages.PersistentMarking.ProtectedSpineFiniteConcreteEnvironmentProof \
  LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredSelectedGuardOrdinaryAddressProof \
  LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitSeparationProof \
  LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInstalledJCharacterizationProof
```

To audit the checked-in evidence without Lean, run
`python3 formalization/verification/reconciliation-2026-11-24/paper16-working-branch/verify_working_evidence.py`
from the repository root. It verifies exact source and archive digests,
checks fresh-source receipt provenance including cache hits, and checks
the archived named axiom outputs. The earliest structural archive
includes only three of the source logs; the tool reports the omissions
rather than treating them as independent axiom checks. For archive and
numbered-register integrity, run the reconciliation validator one
directory above. These commands serve different scopes.
