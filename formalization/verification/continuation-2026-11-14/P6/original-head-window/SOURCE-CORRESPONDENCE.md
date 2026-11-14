# Actual original HeadInWindow

Sources: NumberedFiniteUniverseDefinitions.HeadInWindow/RankedCovered; SourceMarkedSyntaxDefinitions.headArguments/headResult; NumberedHeadWindowPrimrecProof.headWindowPrimitive. The original predicate is ranked-symbol coverage AND original result-type membership AND membership of every original argument type. No substitute size/type window.

The actual AST uses finite arity lookup from numbersNumber(List.ofFn arity), avoiding an assumed selected arity supplier. Valid ranked payload is Fin.val. Application raw payload is Nat.pair(typeNumber sigma)(typeNumber tau), so its arrow type is successor(payload); arguments are exactly [sigma→tau,sigma]. Zero/succ/cases/recursor have no arguments; ranked arguments are replicate(arity s) ground, whose membership condition is vacuous at zero and ground membership otherwise. Original result types come from the paid branchResult AST, not annotations.

NativeWindow covers all six valid HeadCode constructors and arbitrary original symbol/type lists, preserving membership despite duplicates. Numeric symbol lists map Fin.val, numeric type lists map typeNumber; these correspondences must be proved rather than guessed. Unsupported raw tags default to zero, but no theorem assigns semantic validity to malformed payloads. InternalBranch is an actual graph factor from raw-pair equations only, independent of native calibration; finite arity correctness is not reflected internally.

This is the first literal headMove conjunct, not sourceHeads enumeration membership or complete headMove. Original internal extraction/permutation adequacy, global recursive exchange correctness, and source stability remain unpaid. Existing selected tuple unchanged. Frozen before proof for review/preflight.
