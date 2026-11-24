# II5 branch reconciliation, 24 November 2026

## Baselines and scope

The pre-merge main pin was `4028a9e34506f4339af2992749464cf2d4d55eb9`.
The common formalization fork was `dd4eddff9f8eab0a4532e8df4880f71b8d5dffb9`.
Both proof branches descend from that fork and from pre-merge main.

* **Main to common fork.** This is the already published cumulative formalization
  and comparison-paper replacement, including the comparison-editions archive,
  historical registers and evidence. It is inherited, not a freshly audited
  full project or a newly produced 24 November proof.
* **Common fork to newer baseline.** The eight commits ending at
  `a4df2fc9984afa17b6653d90d1c6e669ff97a660` supply the 162/5 baseline,
  including the complete Paper 17 joint evaluator, the Paper 16
  fixed-point manuscript correction, the native iteration result and
  the actual-collapse development. Their original checkout is preserved.
* **Prior branch selection.** Of the 3,124 added paths from the common
  fork to `ff0f88fefe74f978fc40ed6864f11c1f4786bc69`, this reconciliation
  takes 485 exact paths: eight supporting acceptances with their referenced
  evidence and the complete missing local Lean closure (436 files) of
  those proof endpoints. Some of the eight records also pin exact
  failed-source or patch artifacts as evidence; those are kept unchanged.
  No unrelated prior draft or alternate Paper 17 compiler chain is merged.
  The full prior history remains at its pin.

The combined change from pre-merge main to the newer baseline already
contains 72,143 changed paths, mostly cumulative formalization evidence
and sources. No claim is made here to have repeated a line-by-line review
of that whole history. The new reconciliation adds no build-system,
CI, toolchain, dependency-manifest, or paper manuscript edit; these
statements describe the reconciliation delta, not all inherited commits.

## Exact overlap and selected reuse

* **Paper 17:** Retain the newer jointly partial-recursive evaluator in the
  control parameter, policy code and raw query. The selector equation is
  shared with the prior fixed-control compiler. Primitive-recursive currying
  under the pinned code encoding is the narrow route to a joint explicit
  compiler if still wanted; that bridge is not established by this review.
* **Paper 16:** Prior #1685–1686 supply duplicate-preserving certified
  multiset splitting and the literal J union, singleton and typed-member
  results on the concrete original ID₁ checker. The newer functional
  union output and the prior three-input certified permutation test are
  not identified: an adapter must show evaluation and carrier correspondence.
  Prior #2012–2017 add least-representative and two-way arbitrary positive
  application path transport over the actual rank-tested tuple and its
  positive-rank address branch. This does not close the rank-zero address
  branch or full arithmetic accessibility.
* **Record identity:** 1,428 common acceptance files have identical bytes.
  The differing records under numbers 1430–1494 are branch-local.
  [INDEX.json](INDEX.json) maps exact path plus pin for both branches.
  No conflicting prior numbered ID was copied into the live acceptance
  directory, and no old record content was rewritten. A test overlay that
  reintroduced both actual #1430 files was rejected by the ID check.

## Numbered correspondence disposition

The reconciled register is **160 checked / 7 pending, 167 total**. This is
the newer branch's 162/5, with two Paper 16 rows conservatively held for
exact manuscript correspondence rather than removal of the Lean results.

* **Structural interpretation:** Keep the intentional owner-approved
  fixed-point manuscript correction and corrected comparator/underlying
  Lean proofs. Refresh the decision-section hash and the three displaced
  theorem locators. The promotion's own record says there was no whole
  independent comparison of the corrected conjunction. In particular,
  the `FixedApplication` target is for an empty bound context while the
  manuscript describes environments interpreting concrete substitutions,
  and the coverage of printed capture-avoiding substitution by the free
  and literal-binder conjuncts needs a precisely stated comparison.
* **Realization closure:** Printed `ordinals.tex` 435 says realization
  survives replacement by a strict predecessor. The compiled strict
  transport and the printed beta-proof use the opposite implication:
  from the strict predecessor to the original term. Preserve the full
  compiled conjunction as historical evidence; do not represent it as
  checking the printed direction. Leave the current manuscript and PDF
  untouched rather than changing the wording or historical proof pins
  as part of this reconciliation.
* The two records move unchanged to `historical-numbered/`, outside the
  live checked-record bijection. The other four newer promotions remain
  in force. No supporting proof is counted as a new numbered adoption.
Their native gate and source pins are independently cross-checked. The
Paper 17 main receipt pins the source map as it existed before its Outcome
section was appended. The exact 2,135-byte historical prefix is preserved
under this review with the original expected digest; the current expanded
map and native evidence are unchanged.

## Verification boundary

Run `python3 formalization/verification/reconciliation-2026-11-24/verify_reconciliation.py`
from the repository root. It checks the archive manifest, exact numbered
LaTeX statements and source SHA/line locations, collisions, live checked-row
bijection and source/evidence pins. Historical record schemas are preserved.
The old migration verifier still requires a file-valued independent-review
field on every packet; older packets with a native receipt and scope map
already violated that assumption before this reconciliation. Its failure
is not reported as a pass. The focused validator does not retroactively
assert independent review or validate an entire historical build.
Two trailing spaces in byte-pinned imported sources are retained rather
than modifying the historical inputs; all other reconciliation files pass
the standard diff whitespace check.

The selected prior records retain their original standard-axiom receipt
metadata and SHA-pinned source. The original host receipts were checked
against those hashes. New native evidence for the reconciled exact gates is
reported separately, and neither a source hash audit nor those focused
gates constitute a whole-root or published PDF replay.
