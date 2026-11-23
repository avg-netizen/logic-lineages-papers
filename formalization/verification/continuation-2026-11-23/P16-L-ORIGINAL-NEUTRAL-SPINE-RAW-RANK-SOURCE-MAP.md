# Paper 16 (L): strict rank descent on the actual original raw neutral spine

The rank is an inductive relation over literal raw codes: bare free 1,
bare bottom 0, and actual tag6 auxiliary adds one to the rank of its
function (independent of the right argument). An accepted original
raw run returns another code in this relation at a smaller rank.
The main induction is on the literal neutral shape with arbitrary fuel.
Original accepted proper tag5 consumes the actual child at residual
fuel and keeps the exact outer raw right argument. Accepted original
root on a neutral-headed auxiliary is the verified only-bottom case.
Original direct step additionally gives admission of the target.

Gate NumberedWindowNeutralSpineRawRankProof, aliases
exact_OriginalNeutralSpineRawRank and exact_OriginalNeutralSpineStepRank.
No claim about selected least representatives, right-argument exchange,
positive path, arbitrary arithmetic reflection, or an open object rank.
Native pending. Frozen Lean SHA-256:
    d6e6a07f44b28688f8b41d43588b1032e964e39370edbfa2ab771284380a680c  formalization/LogicLineages/PersistentMarking/NumberedWindowNeutralSpineRawRankProof.lean
