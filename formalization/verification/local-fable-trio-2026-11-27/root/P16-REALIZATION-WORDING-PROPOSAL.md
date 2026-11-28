# `lem:realization` — wording decision for the owner (root lane, 27 November 2026)

**Decision needed:** one sentence of the manuscript. No proof work is open for this row.

## The problem

`16-persistent-marking-termination-ordering/sections/ordinals.tex`, line 435, first sentence of the lemma:

> Realization is preserved when a term is replaced by a strict predecessor.

Read literally (from a term to its strict predecessor) this is false: the checked
`Paper16RealizationDirectionProof.exact_PrintedDirectionCounterexample` /
`exact_NotPrintedRealization` (receipt `1795671863201769769-10`) exhibit a closed native beta source whose
countable rank realizes a value that its strict reduct does not realize.

The lemma's own proof uses the opposite direction, and says so (line 447–448): "its application
beta-reduces strictly to the substituted body, so strict predecessor closure transports the body's
realization **backward**." At ι this is just the rank inequality `r(t) > r(u)` for a strict edge `t ⊐ u`:
whatever `u` realizes, `t` realizes.

## What is checked for the corrected direction

`NativeRealizationCompleteProof.exact_FullRealization` (the comparator named
`Paper16RealizationDirectionTargets.BackwardRealization`): the closure clauses with the strict clause read
from strict predecessor to original, downward closure in the semantic value, countable suprema, the full
typed lambda fundamental theorem, and the finite-chain statement of the proof's last sentence.

## Proposed replacement (first sentence only)

```latex
Realization passes from a strict predecessor to the term it precedes:
if $t\cs u$ and $u$ realizes a value, then $t$ realizes it.
```

The remaining three sentences of the lemma and the proof are unchanged; the proof's phrase "strict
predecessor closure" then names exactly this clause.

## If accepted

The row `16-persistent-marking-termination-ordering:lem:realization` can be adopted on
`BackwardRealization` (register 162 checked / 5 pending). The manuscript edit, the PDF rebuild and the
register change are the owner's or the coordinator's; nothing was applied in this round.
