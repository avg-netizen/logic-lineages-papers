# Original decoded standalone extraction: exact2 freeze

## Source correspondence and duplicate check
The existing Continuation20261114/ExchangeSelectedRecursor/Definitions.lean defines
count R = successor of R, finalGraph at [count R, node, parameter], extract =
headCode followed by InternalUnpair.right, and exchange = extract composed with
finalGraph. This packet uses that AST literally. R and D are the checked original
decoded rank and dependencies; G is the fixed ConcreteHeadMoveLayer.layer n arity V.
The actual parameter is unchanged through rank, graph, dependency and layer.

Existing ExchangeSelectedRecursor.InternalProof.internalFinalGraph only reduces
to head/pair-snd extraction; internalSingletonValue assumes singleton/pair graphs.
Neither proves final singleton shape. StandaloneCacheExtraction is the separate
argument-entry recursion with projection rank and different D/G, not this result.
Current OriginalDecodedCacheCoherence transports lookups but does not connect
literal selected extraction to lookup. These endpoints discharge that gap.

## Exact obligations
1. Actual R(node,param)=rank and actual graph at successor rank imply equivalence
between literal exchange output value and first-match lookup successor value.
2. The same equivalence for any actual aligned cache (bounded index, actual
rank(seed), actual subtraction, frontier/member and successor table).
No native table image, valid pair, singleton, Some or lookup agreement premise.
All raw nodes/parameters and arbitrary fixed V are quantified.

## Constructive plan
Root proof: query actual previous graph, singleton frontier [node], dependencies,
ordered answers and layer output. subtract(rank,rank)=0 and bindList depth0 give
literal singleton frontier. Paid optional nonzero splits the layer output as
successor payload, including payload0. The actual filterMap stage is therefore
the singleton encoded pair(node,payload), proved by original stage equations.
Graph functionality identifies this singleton with the observed final table.
Existing extraction and first-hit laws plus functionality prove both directions.
Aligned proof: introduce actual own rank/final table and singleton frontier
internally; instantiate both directions of paid all-raw cross-root coherence.
Root boundedness/reflexivity, subtraction and membership are internal duties.

## Limits
This does not calibrate V to the original decoded window guard, prove native
layerValue correspondence, install the original supplier tuple, or complete E.
It does not yet assert a fully standalone recursive dependency-answer equation;
ordered mapGraph semantics are preserved in root construction, not replaced by
an external list assumption. Current coherence passed exact/native checks;
independent acceptance is pending at freeze time. No proof authored before review.
