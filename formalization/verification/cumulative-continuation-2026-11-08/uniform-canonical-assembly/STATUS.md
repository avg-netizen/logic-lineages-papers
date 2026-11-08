# Checked uniform canonical assembly — 8 November 2026

This continuation closes the uniform canonical-package gap recorded at
`acd4c2b489324f8a634fef745912ae99d5c6aac3`. One original four-leaf selection,
with an explicit normalization of its membership field, is fixed before every
source window and ambient Gamma. The same resulting Programs satisfy both the
internal laws and the original all-input calibrations.

## Completed proofs

| Component | Exact targets | Result |
| --- | ---: | --- |
| [Uniform descent selection](../uniform-descent-selection/STATUS.md) | 9 | Original source/target validity, fallback representative and typed-checker calibration; internal factorization, canonical output and source application closure; one uniform selection. |
| [Parameterized canonical fold](../parameterized-canonical-result-fold/STATUS.md) | 4 | Internally certified output existence, validity/type/transition-fixedness, typed output, and representative application transport at the same symbolic parameter. |
| [Original fold calibration](../uniform-canonical-result-fold/STATUS.md) | 2 | The actual bounded fold equals the original packed-target representative on every natural input; the whole-state success checker accepts every run; one tuple combines calibration and internal laws. |
| [Context-only membership](../uniform-context-membership/STATUS.md) | 4 | Original raw membership ignores the Gamma coordinate; a concrete normalized Program preserves full leaf calibration and has an internal symbolic-context slice; the normalized tuple retains the complete package. |

The fold uses the original stack and `2*payload+1` fuel. Strong induction bounds
the original input payload, while input, type and parameter remain quantified
inside its predicate. Each application carries the same parameter to both
children. The actual application program takes the supplied function output
and the raw argument; it normalizes the argument internally. Neither a fixed
argument nor fold idempotence is a premise.

All-input calibration includes malformed packed values and decoded values
outside the source universe. The original packed-target representative remains
the fallback at unopened nodes. The success theorem includes a zero result.
Internal derivations are proved separately from external evaluation equalities.
For the generic application rule, actual codomain membership is retained as a
local premise. The new membership slice makes its Gamma independence available
through the literal Program graph under `parameter = pair(context,gammaCode)`.

## Verification

All **19 frozen exact aliases** and the focused aggregate
`LogicLineages.ExternalCheckpoint20261108UniformCanonicalFold` passed. The
continuation adds **31 component Lean files and one aggregate**. All 19 exact
aliases and 117 additional own-namespace declarations use only `propext`,
`Classical.choice` and `Quot.sound`. Every new component source has a matching
successful native compile row. All frozen Definitions, Targets and named
supplier hashes are unchanged.

The serialized profile remains 2048 MiB heap, 1536 MiB process-tree RSS,
2048 MiB minimum free memory, one thread, 90 CPU seconds and 180 wall seconds
per compiler. Peak new-source RSS was **1,262,884 KiB**. Dependencies and CI were
unchanged. This evidence covers the focused gates and aggregate; it does not
assert a full-root or remote-CI build. Earlier verification packets remain
preserved, and the new evidence keeps only current component rows and focused
native receipts.

## Remaining source obligation

The numbered register remains **168 checked, 2 inherited, 19 pending / 189**.
These are supporting results for paper06 `lem:id1`.

The next step is to carry this same normalized package through parameterized
typed-edge, vertex and path lifting, then the original outer object wrappers.
The original certified-lift antecedent supplies a shared runtime Gamma code;
it does not imply equality to a preselected Gamma. The wrapper must bind that
code internally and construct `pair(context,gammaCode)`, eliminating the
fixed-object-fiber restriction by a uniform derivation.

After the original unqualified `CertifiedApplicationLift` is proved, the
existing full-type downward-closure consumer applies. Original source
multiset, constructor, lambda, structural substitution and the closed endpoint
`ContextUniformTargets.ActualContextUniformInternalAccessibility` still remain.
See the [concrete next steps](../uniform-canonical-result-fold/NEXT-STEPS.md).
