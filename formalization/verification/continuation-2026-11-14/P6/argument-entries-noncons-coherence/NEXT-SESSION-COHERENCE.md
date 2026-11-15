# Remaining original cross-root coherence induction

Compare node cache in graph(k,seed,param) at frontier depth
 d = seed - (k-1) with node's own-root final graph(node+1,node,param).
Use actual subtract graphs, never an informal index substitution.

1. FrontierRank gives d+node <= seed. For a child, predecessor membership and
   strict raw-rank descent give child<node and membership at depth d+1.
2. Pay subtraction/order arithmetic that previous graph(k-1,seed,param)
   covers exactly that depth and retains enough stage capacity. For a nonempty
   dependency case this includes proving k>=2, not using a predecessor as if
   it were successor without evidence.
3. Form an object-language strong induction invariant comparing two actual
   caches for the same raw node across roots/budgets, with each frontier
   membership and index/depth alignment explicit. Internally eliminate table,
   dependency and answer witnesses. Do not substitute an independent child
   extraction for a previous-table lookup without applying this invariant.
4. Non-cons local base (this packet if accepted) includes all malformed raw
   tag6 payloads; canonical nil alone is insufficient for an all-raw invariant.
5. Cons local step uses TailCoherence: tail cache equality is an IH duty; head
   cached values need not agree but both must be present. PreviousCoverage
   supplies presence only after exact index/depth arithmetic is established.
6. Connect final singleton stage/extraction only after actual cache coherence;
   then separately pay typed spine Some-definedness. Native valid-code
   calibration does not supply any of these internal claims.

Actual first-match/duplicate semantics, omission of missing map keys,
outer Some0 vs missing0, and source-rank subtraction order all remain fixed.
Global E/class coherence/source stability remains open.
