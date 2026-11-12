# Proposed next contract: visit-step scheduling only

Design proposal, not frozen or implemented.

## Frames and state

A visit frame carries the exact job `pair(raw,pair(c,Gamma))`. A return frame
carries that original job, the raw-child count, and the context-deletion count.
Use disjoint tags for visits and returns. Keep work and results as separate
encoded lists; no result is consumed on a visit step.

For a native raw state `s` and window `c`, write `Visit(c,s)` and
`Return(c,s,length(children s),length(s.context))`. The proposed precise native
transition equation, for arbitrary work suffix `rest` and results `results`, is:

```
step (Visit(c,s) :: rest, results)
 = (map (Visit c) (WorkBound.successors s) ++
       Return(c,s,children(s).length,s.context.length) :: rest,
    results)
```

The concrete step must use the checked expansion Program, a bounded list map
that adds the visit tag, and actual append/cons Programs. It must not enumerate
native syntax inside the runtime. A separate full-vector numeric equation
specifies malformed state/frame behavior; initially unsupported return frames
should preserve the complete state rather than pretend assembly succeeded.

## What this proves and does not prove

This is a single visit macrostep simulation, preserving the original window in
every scheduled job and in the return frame. Child jobs precede every context
deletion; duplicates and the lambda child's cutoff-zero deletion remain.
The return frame retains the boundary between raw child results and deletion
results. The contract has no oracle for those results.

This does NOT yet prove that a return frame can assemble the intended semantic
signature. Raw argument-list nodes have no typed-term observation assigned;
numbered BASE sorting, extras ordering, and lambda context changes require
explicit return algebra. It is not valid to reuse `layer R Q` with a recursive
self-reference substituted for the literal Program `Q`.

## Separate administrative count

One expansion visit and one eventual return per raw-worktree node would give
at most twice the checked abstract visit count for those two macrosteps alone.
Do not state this as a concrete transition bound until the transition actually
performs each expansion as one total subprogram call and its stack simulation
is proved. Mapping/appending the agenda, decoding, sorting and primitive
arithmetic have separate costs. If they are exposed as small-step machine
operations, introduce a separate administrative potential rather than charging
them zero or recycling the tree-depth bound.
