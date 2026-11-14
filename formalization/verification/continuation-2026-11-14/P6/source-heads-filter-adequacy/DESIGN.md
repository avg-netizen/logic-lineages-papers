# Internal source-head filter adequacy (exact2)

OriginalSourceHeads.Definitions filterStep uses actual OriginalHeadWindow.window at the head and the literal branch zero→tail/nonzero→cons. filterHeads is its original right fold. sourceHeads composes this filter with actual rawWindow; member uses actual numeric contains. No replacement algorithm, sorting or deduplication.

Exact InternalFilter states all numeric lists: given actual filter and queried-window output graphs, contains(output,needle)=1 iff contains(raw,needle)=1 AND window-output≠0. Both conjunction and negation are object-language formulas. No Boolean range hypothesis. Proof requires internal list-code induction, true structural head equality/inequality cases, query transport/functionality, and actual zero/successor split; native list evaluation cannot discharge it.

Exact InternalSourceMember composes this with actual rawWindow graph and existential elimination of the actual filter output. No arithmetic term extraction from mere derivability.

Not proved here: original rawWindow enumeration completeness for typed heads, internal typed adequacy of window or decoder V, semantic argumentEntries extraction/permutation, global recursive exchange or stable classes. Native source-head calibration is not used as an internal oracle. All original list order/duplicate semantics remain untouched. No proof authored/compiler launched before review.
