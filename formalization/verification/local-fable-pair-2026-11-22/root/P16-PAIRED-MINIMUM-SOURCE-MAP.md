# Paper 16: opposite paired parent exchange forces equal successful leasts at the applications

Serves the Paper 16 "Next" item of `../../continuation-2026-11-22/SESSION-HANDOFF-2026-11-22.md`
("compare the actual minima") on the way to internal arithmetic matching for
`lem:arithmetic-accessibility`. Supporting only; no numbered promotion.

Frozen target `NumberedWindowInternalCoverCombinedRestrictedPairedMinimumTargets.lean`, three statements,
all on the same chosen `P = combinedPrograms s V TV M M0 B T`, `W = thinMatchingWindow P.cover s P.W P.V`,
`X = guardedExchange P.cover s (thinPairedExchange (directedX base P.V))`, and the two applications
`a = auxiliaryTerm dom cod f arg`, `b = auxiliaryTerm dom cod g arg`:

1. `ExactOpenCoverCombinedRestrictedPairedEdge` — from both type-guard conjunctions, the argument
   window, the directed parent edges f→g and g→f at `rawCons dom cod`, and one shared
   `selectedMeasure P.R` value at `a` and `b`: the guarded auxiliary edge `edgeGraph X W ctx cod a b`
   as a plain derivation in the original context. (Record #1379 had it only inside a continuation
   together with the cover reports.)
2. `ExactOpenCoverCombinedRestrictedPairedEdgeMinimum` — two opposite such edges and two held
   successful least calls at `a` and `b` give `eqn x y`.
3. `ExactOpenCoverCombinedRestrictedPairedParentMinimum` — the same from the parent hypotheses of (1).

Proof: (1) is #1379's continuation applied with the edge itself as goal. (2) is accepted #818
`exact_MutualEdgeMinimumEquality`, which holds for every `guardedExchange C s baseX` and every window
with no cover, pool or length input; the combined restricted paired exchange is literally of that form.
(3) applies (1) in both directions — its hypotheses are symmetric in f and g — then (2).

Consequence for the plan: the route through mutual inclusion of the reached pools
(`exact_MembersSeedInclusion`, #1385's reach) and the packed lower bounds is not needed for equality
of minima on a paired edge.

Not claimed: existence of either least (both calls are held); removal of the shared measure
hypothesis; anything along a path of several exchanges; transport between different raw
representatives of one function class; any unrestricted-window or protected-port statement.
