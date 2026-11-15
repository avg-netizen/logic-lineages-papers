# Exact original decoded-window validity (three frozen contracts)

The original TransparentExchangeLayer.validValue checks successful decoding of
Node at input0 and Window at input2, ignoring the answer-list input1. Node validity
is already paid by the original code guard on the two original product coordinates.
Window is literally List(Fin n) × List Source.Ty under its original instances.
HeadMoveFields.EncodingProof.windowComponents is only conditional on successful
decoding; it does not supply a checker or all-input validity characterization.
OriginalHeadWindow tests head membership/closure in an already supplied window,
not this decoder predicate. No duplicate original window validity AST found.

AST: encoded raw-list recursion, base constant1, step conjunction of head<n and
recursive acceptance; no parameters. Window applies this to original unpair-left.
Type-list decoder totality must be proved from the actual Source.Ty instance and
original Encodable list recursion, and cannot be assumed from an alternative
numbered decoder. Fin decoding must use the actual bound test and list codec.
Native contracts quantify every vector/raw code, including n=0 and invalid lists.
The internal contract is graph(symbols n,1,raw) iff all actual list members are
strictly less than numeral n. It requires constructive raw-tail induction and
actual membership head/tail cases in both directions, not reflection of native
calibration. Duplicate/order behavior follows literal list recursion.

Planned proof: exact Encodable list decoder recursion with Fin decoder, and total
Ty decoder, prove native all-raw via strict raw-tail induction; independent
internal raw-tail induction builds the universal member characterization using
actual conjunction/listRec/membership equations. Binder syntax separately staged.

Still unpaid: compose node and window checks into literal V calibration; concrete
layer all-input calibration/installation; overall original E/I/C/accessibility.
This is syntax validity, not HeadInWindow, ArrowClosed, or typed acceptance.
No proof authored before target/preflight review. Previous standalone exact2 has
passed native verification, independent acceptance pending at this freeze.
