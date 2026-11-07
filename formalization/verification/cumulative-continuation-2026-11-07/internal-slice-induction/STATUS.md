# Checked internal single-slice induction

Date: 7 November 2026.

Both frozen exact supporting targets passed in the original one-body
`InternalCalculus.Derivation`:

- `ActualInternalPairedClosure`: independent literal scalar/multiset closure
  derivations produce the original combined-body tagged closure derivation.
- `ActualInternalSliceInduction`: membership in either original tagged slice
  implies an arbitrary full-language invariant from only that slice's closure
  derivation. The unselected slice closes internally from the original I/J
  fixed-point equation.

The result preserves arbitrary predicate polarity, free parameters, assumption
contexts and symbolic instantiation terms. The calculus still has exactly the
one original combined source body; `sliceBody` is syntax for a closure premise,
not a new inductive definition.

## Reusable syntax and proof interfaces

`InternalSliceInductionSyntaxProof.sliceReplacement` identifies the selected
closure premise with the exact original carrier and a universal implication
from the original arithmetic successor relation to the arbitrary invariant.

`replacementBranch` transports predicate replacement through the literal tag
guard. `tagReplacementSelection` transports selection through the entire
original positive grammar. `branchTransport` preserves the external parameter
context while binding the invariant object. These are syntax equalities and
actual derivations, with no reflection of standard-model truth.

## Acceptance

The final focused coordinator passed under pinned Lean `v4.32.0-rc1`, one worker,
2048 MiB heap, 1536 MiB process-tree RSS and the unchanged 2048 MiB free-memory
floor. The successful final run observed peak process-tree RSS 1,225,252 KiB.
Its exact aliases both report only `[propext, Quot.sound]`.

The retained compact evidence is `FINAL-CHECK.json`, `FINAL-CHECK.log`, the frozen
target text/hashes and the accepted six-source hash manifest. The earlier
namespace-opening and parenthesization corrections preserve the initial texts
and hashes with explicit explanations in `FROZEN-TARGETS.md`. Routine failed
compiler logs remain in the ignored build-report directory.

## Source scope

This supports paper06 `lem:id1`: the source uses independent I/J induction for
inverse application, lambda closure, multiset union and singleton membership,
and constructor base/extra multisets. The new rule removes the prior whole
combined-body closure burden for each of those inductions. Their remaining
source-specific closure proofs and the all-term endpoint remain pending.
No numbered source statement or global register entry is promoted.

The root coordinator owns the final aggregate check and shared integration.
