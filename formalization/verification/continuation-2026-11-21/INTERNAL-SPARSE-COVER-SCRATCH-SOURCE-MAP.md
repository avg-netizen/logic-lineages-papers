# Paper 16: selected source cover to standard scratch

## Original cover and its unchanged selected program

`16-persistent-marking-termination-ordering/sections/ordinals.tex` 70–77
allows the original finite primary classes to be effectively enumerated
and a least code selected. This target supplies only the numerical codec
boundary for the original **ordered supplied cover**. It does not prove
a full least algorithm or any ordinary open graph semantics.

The source `NumberedWindowCoverBoundsAlgorithm.cover H K n` is an
`Option (List Nat)`: it is `none` at failed original syntax and
`some` of the actual original grammar list at its measured bounds
otherwise. The selected #520 program is precisely
`NumberedWindowCoverBoundsProgramChecks.exact_SelectedCoverProgram`:
one physical Program3 works at every tape
[Encodable.encode H, Encodable.encode K, n], returning the original
`Encodable.encode (cover H K n)`. The unchanged official target names
the full Option output, not the unwrapped sequence or a Boolean.

`ActualSelectedCoverOutput C` repeats exactly that calibration for the
same selected C. The physical `coverOption C s` merely uses original
literal constants for `Encodable.encode s.window.2` and
`Encodable.encode s.types`, and projection 0 for the actual seed n.
The original fixed Settings are not replaced, and `coverOption`
returns the original entire Option code before any scratch projection.
No source success is inferred from the scratch output.

## Exact codec boundary, including genuine some []

The pinned Mathlib `Encodable` instances are the ones already used by
the selected cover: `Logic.Encodable.Basic` gives Option none=0 and
some=successor of the payload encoding, and `Logic.Equiv.List` gives
`Encodable.encodeList [] = 0` and a cons via successor of
`Nat.pair (Encodable.encode head) encodedTail`. For natural elements
the encoding of the head is that same natural. This matches exactly
`NumberedMultisetNumeric.numbersNumber` (actual nil 0 and
`1 + Nat.pair head (numbersNumber tail)`) by list induction, preserving
order, duplicates and actual entries. There is no format guess or
conversion via a different permutation or polynomial raw field codec.
The checked dependency lock is pinned; these are not new instances.

`optionPayload` is the original physical branch on unary projection 0,
with literal zero on zero input and the actual predecessor on the
nonzero input. `ExactCoverOptionPayload` calibrates that literal program
on each actual `Encodable.encode p` to
`numbersNumber (p.getD [])`. In particular none encodes to 0 and a
valid empty list as some [] encodes to 1 at the actual original source
boundary. Those distinct source codes are preserved by `coverOption`;
only the explicit scratch projection maps both to nil. No further
validity or source success follows from that nil output (or is needed
to read this projection).

`ExactSelectedCoverToScratch` chooses the same C once with the full #520
all-head/type/seed calibration. For every s and n it retains the exact
original encoded `coverOption` and the exact scratch encoding of
`NumberedWindowScalarAlgorithm.vertices s n`, which is precisely this
original cover with `.getD []`. `scratchVertices` is the physical
composition of the above codec with that same term, not a fourth
independently selected oracle. This does not filter or modify the original
ordered list in any other way.

## Proof boundary

Later numeric proof suppliers: the actual #520 selected exact alias,
the existing literal constant evaluation, the original branch and
predecessor evaluations, and an explicit comparison of the two actual
list encoders. No prospective proof imports are needed in this frozen
target closure. No round, least, minimum, fixed edge, raw matching,
signed/object graph interpretation, or numbered result is included.
