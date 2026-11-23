# Paper 16: internal occurrence elimination for the ordered insertion scan

Source: `16-persistent-marking-termination-ordering/sections/ordinals.tex`,
lines 74–76, 84–98 and 142–150. This is pointwise elimination from an
actual member graph, not a permutation or J theorem.

The only varying term of the first-order induction motive is the original
ordered scratch-list code. The chosen callback r, raw removed-list code and
candidate entry remain fixed at their actual object terms. In the zero case,
the actual scratch membership loop cannot accept. In the cons case, the same
checked scan loop yields actual head acceptance and actual tail acceptance.
The original membership loop jointly yields either a genuine head match or
membership in the actual tail. Head equality is transported at precisely
the row slot of the accepted callback; the removed tape remains unchanged.
Tail membership applies the internal induction hypothesis. The conclusion
is through the original ListInduction derivation schema, not external
enumeration of a list of object terms or numeric reflection.

One checked premise is acceptance of the same selected scratch loop.
Another is the original actual scratch member graph, not a synthetic
occurrence or index. The resulting row can feed the independent
unconditional exact row-cases theorem. This packet does not assert
counting, indices, partition, installed d, arbitrary J injection, or an
automatic actual scratch member for an arbitrary value.

Native candidate (pending):
`LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberChecks`.

Exact authored source SHA-256:
- 744d945d6f25fefee31ff16d7a16caa5b09c64c28cd1cda6876219486f26884d  LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanMemberChecks.lean
- 018ea49a3cdd15b8ca2d229424394228b19ff4d90234fdba91abe6239869adda  LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanMemberProof.lean
- 3a77e07560d2ad03ada391a965178493e1fe5c7f8343b7675454f17e833a06e8  LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanMemberSyntaxProof.lean
- 3308049b4dd95943b4e816c25ecd19e62afb8469c40e2219a59f0d44ecc4de40  LogicLineages/PersistentMarking/NumberedWindowInternalDirectInsertedScanMemberTargets.lean
