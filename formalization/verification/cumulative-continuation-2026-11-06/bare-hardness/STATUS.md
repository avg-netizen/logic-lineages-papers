# Accepted finite depth-two comparison and bounded-vector obstruction

The continuation from `b09ce88d19ff57fa6a0fac921dd3513d51e1a935` completes two
original paper 02 source statements:

| Source label | Exact frozen endpoint | Result |
| --- | --- | --- |
| `thm:finite-bare-hardness` | `Targets.FullFiniteBareHardness` | Strict and weak value and norm comparison are Pi01-complete on the exact positive finite exponential fragment at depth at most two. |
| `thm:bounded-bare-vectors` | `Targets.FullBoundedBareVectors` | Strict and weak original WW comparison are Pi01-hard and undecidable on computably constructed bounded two-component C-vectors with finite depth-two higher components. |

The Lean namespace is
`LogicLineages.ComputabilityKnowledge.BareHardnessCompletion`.

## Mathematical scope

The scalar reduction covers the complement of every recursively enumerable
predicate. Every reduction output is a well-formed source instance, including
outputs for nonsolutions. A matching co-RE upper bound explicitly accounts for
malformed and over-depth inputs before searching genuine positive tuples.
The same outputs prove both actual value and actual ordinal-norm comparison.
All terms remain positive finite under the original occurring-name admissible
substitutions and belong to every source class `C_i`, `i >= 1`.

The vector reduction uses the unchanged source construction
`(H,V+1)`, `(H,U)`, `(H+1,U)`. Its bounded norms and C membership are proved
uniformly, and both vectors have exactly two components. Strict comparison is
the original relation: strict at zero and weak at positive indices. The
undecidability theorem excludes even a total computable procedure required to
be correct only on the certified genuine input domain.

The accepted Diophantine representation already supplied the mathematical
foundation. This checkpoint exposes a well-formed computable polynomial family
for every RE predicate and assembles the existing domain conversion, circuit
comparison, original-substitution transport, and literal vector padding.

## Verification

- The frozen target preflight passed before candidate proof authoring.
- The focused coordinator `LogicLineages.ExternalCheckpoint20261106BareHardness`
  passed in `receipts/1793930511644755998-2.json`.
- All **298 local source modules** in its dependency closure match successful
  native rows and current local artifacts.
- All **19 exact statement aliases** passed transitive axiom audits using only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Peak successful observed process-tree RSS was **1,395,248 KiB**, below the
  unchanged **1,536 MiB** cap. The single-worker, 2,048 MiB Lean heap, 90-second
  CPU and 180-second wall limits remained unchanged.
- Pinned upstream objects came from the official cache. No upstream compiler
  rebuild was performed.
- Failed attempts, original candidate snapshots, and exact local repairs are
  retained. Repairs changed proof normalization and one missing preflight
  import; no accepted source contract changed.

This is a focused native acceptance. No full-root build or remote CI pass is
claimed. `NATIVE-VERIFICATION.json` records source hashes, actual axiom closures,
raw receipts and module-specific resource observations.

## Register and preservation

The two numbered statements move from pending to checked. The resulting
register is **166 checked, 2 inherited, 21 pending / 189**. Every other numbered
statement and all 189 source statement texts remain unchanged.

All prior Lean sources, manuscript files, compiler configuration, dependencies
and CI files remain unchanged. The earlier finite-source comparison and uniform
kernel-separation proof/evidence packages are preserved. Paper 02 remains in
progress because its broader consumer corollary is still pending. Paper 08's
full first-order BASE and polynomial-word comparison obligations remain open.

Read `SOURCE-CORRESPONDENCE.md`, `ACCEPTANCE.json`,
`ACCEPTANCE-REVIEW.json`, and `PUBLICATION-VALIDATION.json` for the exact scope,
source review, and register reconciliation.
