# Source map: actual bounded ordered-field parser and open symbolic rows

Paper 16, `ordinals.tex` 12–29, 70–76, 84–98, 112–127 uses all finite
contexts and literal numerical certificates for actual quotient paths.
Here the authoritative parser is the actual field coder:
`NumberedWindowFieldAlgorithm.unpack n = finish (steps n (some (n,[])))`.
Its failure is absorbing, a zero cursor stays successful, and a successful
outer cell reads the actual sparse polynomial decoder and pushes its head
into the reverse accumulator. A valid outer cell can have a malformed
tail. Both its exact optional result and decoded order matter.

The new explicit arithmetic AST reads the same raw code and raw tail.
At scratch stage i+1, it first tests the actual selected outer cell.
Failure makes row 0. On a recognized cons it looks up the older raw tail
row t at lag i-t: sparse raw tail descent guarantees t <= i. A rejected
tail makes row 0, otherwise it prepends the actual original head to the
decoded tail in proper order. The positive payload is one plus an ordered
scratch-list code; zero is failure, and one is successful nil. The scratch
store and scratch payload use the retained total Nat.pair list code, only
as arithmetic state/output representation. They never replace the
original polynomial pairing or field/certificate inputs. The two memo
parameters are explicitly fixed to zero for the unary selected parser.

`ScratchBridge` retains exact scratch roundtrip of all ordered lists.
`BoundedOriginalFuelAccumulator` states equality with the original
bounded state loop at any sufficient fuel and prior accumulator; its
result includes that accumulator's reversal as a prefix. `OriginalUnpackCases`
gives the exact original nil/gap/sparse-cons equations. The two whole
numeric gates give the exact selected code for the original optional
result on *all* inputs, and exact decoded optional list equality. They
include recursively malformed tails, not only successful code values.

The four open contracts are actual proof trees in the original finitary
ID1 derivation system. They pay nil, nonzero/no-cons malformed, both
directions of the selected parser graph's real cons/tail relation, and
rejected-tail propagation. Inputs and witnesses are arbitrary free terms.
The constructor premise remains the original sparse `fieldCons` graph;
the source state machine or standard-natural facts are never imported
into the object calculus as axioms.

The generic scratch table ASTs coincide with the retained
`ExchangeRowMemo` generic base/step/table/row specialization, except for
the append-only names. One may reuse its actual tail/drop/lookup proofs
on the very same AST after explicit conversion, or thin their generic
arithmetic implementation without altering any prior file. The exact
application uses real subtraction on the strictly smaller raw tail and
the actual arithmetic lag equation. No prior parser AST or `sourceBody`
is silently changed by numeric equality. This does not yet prove
typed-context invariants, actual positive path fold, local hop/least
transport, full arithmetic matching, or the numbered ID1 theorem.
