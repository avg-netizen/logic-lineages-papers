# Paper 17: canonical signed routes — per-row guards and both directions

Key: `STAGE-CALLBACK-CANONICAL-ROUTES`. Targets module
`LogicLineages.PermittedControl.StageCallbackCanonicalRoutesTargets`.

Printed source: `17-permitted-control-canonical-comparison/sections/arithmetic.tex`,
`thm:arithmetic`, subsection "A finite charge and the order normalization loop": "Normalize an order
atom by the following finite procedure … If z has no remaining nonlinear occurrence, retain the
entire row as a linear row in z … Otherwise … branch on the weak order of their full cores … A zero
combined coefficient is canceled … At a nonzero coefficient it stops by the following domination
argument." Handoff item (a): "make the emitted per-row guards characterize genuine successful reads
and the requested terminal polarity, including ordered availability, signed order/equality".

## What is stated

A route tree `routes top test positive fuel s` on the *first-occurrence* grouping
(`groupTyped`) of one signed row's literal syntax, built only from accepted canonical pieces:
`ActualFiniteFullValueGuards.compile` on `pairs (labels (groupTyped terms))` for guards,
`maximalCoefficient (groupTyped terms)` for the class coefficient, `canonicalSuccessor` for zero
edges, `canonicalPacket` for the linear exit. It reuses the accepted `Route`, `RouteHolds` and
`prefixGuard` so that `ActualSelectedSignedRoutePacket.packet` renders it without change.

Only stopped candidates are leaves (see "Design decision" below).

Targets:

- `ExactCanonicalRouteLayout` — exact membership description of the tree.
- `ExactCanonicalRouteShape` — every guard and terminal is a prepared input; no semantic hypothesis.
- `ExactMatchedAnswerUnique` — at one valuation the true answer tape of a pair list is unique.
- `ExactCanonicalReachedLinear` — at a genuinely reached inactive node the linear leaf holds iff the
  requested signed test holds, either polarity.
- `ExactCanonicalReachedGuards` — at a genuinely reached active node: a guard holds iff its tape is
  the true comparison tape of the successful reads (`Matches` at the updated valuation); some guard
  holds; a holding guard carries the genuine `CanonicalZeroWitness` with the literal symbolic
  successor, or the requested polarity of the row equals that of the nonzero coefficient.
- `ExactCanonicalRouteSoundness`, `ExactCanonicalRouteCompleteness`,
  `ExactCanonicalSufficientRoutes` — some route holds iff the signed test holds, at the syntax budget.
- `ExactCanonicalRoutesAcrossReplay` — the same equivalence stated for a source syntax under the
  accepted `LowerSetup` and `replayMinimum` plus the static sign payment
  `inputSignBoundCode r s.constant (s.terms.map encodeWeighted) ≤ z`.

## What is assumed

`CanonicalContext` = the accepted `RunContext` (selection, strict lower valuation, greatest value
above it, live initial reads, rank bound, long counts, paid transfer tail, paid comparison ceiling,
paid legacy sign ceiling) **plus** `inputSignBoundCode … ≤ z`. The extra payment is real: the
canonical sign funding (#1378, #1383) is stated for it, and it is not implied by the legacy
`terminalCutoffCeiling` (the accepted dominance goes the other way). The stage bound provides it
through `rowBound`; that step is not part of this key.

## What is not claimed

- Congruence rows: untouched here. They already have one exact literal-order packet
  (`ActualGreatestCongruenceRoute.packet`, `exactGreatestCongruencePacket`).
- No `SupplierExact` instance yet: assembling these routes and the congruence packet into a supplier
  for `STAGE-CALLBACK-SUPPLIER` is the next key.
- The tree is a typed, `noncomputable` definition in depth-first order. No raw program is given and
  no claim is made that a raw program emits this order; `SupplierExact` depends on membership only,
  so a level-order raw list with the same members is what S4 has to produce.
- No statement about routes at states that are not genuinely reached from the initial read state.

## Design decision recorded before freezing (root's question)

Proper prefixes of a genuine trace: the fix is in the **list**, not in a falsity terminal. A node
contributes leaves only when it stops — its linear packet if inactive at the greatest rank, one
signed leaf per nonzero-coefficient tape if active. A node whose tapes all continue contributes
nothing by itself. Reasons:

1. Either choice needs the node's own status (active at `top`? coefficient zero?). With that status
   in hand, omitting a leaf is strictly less work than emitting a falsity packet, and it keeps the
   Cartesian join smaller.
2. One call of the accepted raw node (`ActualRawCanonicalNode.groupedCode`) returns the coefficient
   and the optional successor together, so "leaf or child" is a single case split per tape.
3. The accepted raw step (`stepCode`, `prefixes`) does not take `top` and therefore continues
   through nodes that are inactive at the greatest rank. Those continuations are not genuine
   canonical steps (`PreparedStep.active` is required), so the supplier's raw iteration must test
   activity at `top` in any case and cannot be the accepted `prefixes` list unchanged. The typed tree
   here stops at inactive nodes for that reason.
