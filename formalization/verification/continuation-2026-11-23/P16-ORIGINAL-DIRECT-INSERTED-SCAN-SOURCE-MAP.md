# Paper 16: ordered direct-witness insertion scan

Source: `16-persistent-marking-termination-ordering/sections/ordinals.tex`,
lines 74–76, 84–98 and 142–150. This is the insertion-check scan, not
permutation/retained counting, current checker installation or J induction.

The literal scan selects the genuine original sparse input parser for the
inserted tape and rejects parser failure. On success the unchanged ordered
scratch list is consumed by the original listRec table/loop; each row uses
the already checked selected per-insertion callback on that same physical
raw row and unchanged raw removed tape. All-numeral equality uses literal
List.all on the actual ordered unpack, preserving order and duplicate rows.
The removed-tape parser and r are unchanged from the selected callback.
Vacuous nil acceptance concerns this scan alone, not whole valid witnesses.

In the object calculus, the chosen parser's actual successful report
identifies the same scratch code in the accepting scan. Its physical
loop accepts nil and, given a genuine scratch cons graph and acceptance,
yields acceptance of the actual head callback and the actual recursive
tail scan at one. The tail result is recovered from the loop's existing
existential cons transition, not supplied as a numeric assumption.
No all-row internal occurrence induction, all-field report synthesis,
multiset partition, new selected d or membership conclusion is claimed.

Native candidate (pending):
`LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanChecks`.

Exact authored source SHA-256:
- 5ec25c1a2ac9b543d2f8c53bbe3c861cad3112caf9b69074648b4f766d8d5f2d  LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanChecks.lean
- bc9532265cf8c2fa52d5cd6b5bf6ea95acab8b4e1711826bcef9529dfc925b8a  LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanNumericProof.lean
- 7e829404dc49f1c9ac5bdf987f06fd2ca0e1c96835606fd2fec1e71b55fbf94e  LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanOpenProof.lean
- 5e376df2e67a2c3f1417fb552e4cd54290b4db45e549c7db92581b8c77106d4f  LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanTargets.lean
