# Paper 17: the canonical supplier in the list order of a raw level iteration

Key: `STAGE-CALLBACK-LEVEL-ORDER`. Targets module
`LogicLineages.PermittedControl.StageCallbackLevelOrderTargets`.

Printed source: `17-permitted-control-canonical-comparison/sections/arithmetic.tex`,
`thm:arithmetic`: "Each node has finite branching. Thus the entire symbolic normalization tree can be
generated before numerical tails are chosen." This key fixes *how* that tree is listed so that a raw
program can list it the same way; it adds no new semantics.

## Why

`Emits alt B high` is a literal list equation. #1395's `canonical` lists a signed row's alternatives
depth-first, by a recursion in which the fuel-`n+1` tree calls the fuel-`n` tree at varying syntax.
A primitive recursive raw program iterates one level step on a list instead (as the accepted
`ActualRawCanonicalZeroPrefixes.level` does). The close step needs one supplier whose list is the one
that iteration produces.

## What is stated

- `Entry = List Packet × SyntaxState` (guards met so far in path order, current syntax): the typed
  shadow of a raw entry (list of packet codes, raw syntax).
- `children top e`: the zero-edge successors of an entry, **only if** its syntax is active at `top`
  (the test the accepted raw step lacks); `leaves top test positive e`: its linear exit if inactive,
  its nonzero-tape signed leaves if active; `level` iterates `children` by `flatMap`;
  `levelRoutes fuel` lists the leaves of levels `0,…,fuel`.
- `levelOrder`: signed rows get `(levelRoutes …).map (packet …)` at the syntax budget of the cleaned
  syntax; congruence rows keep the accepted packet.

Targets: `ExactLevelOrderRoutes` (same routes as the #1394 tree, as sets),
`ExactLevelOrderMembers` (same packets as #1395's `canonical`, per row),
`ExactSupplierMemberTransfer` (shape and exactness of a supplier depend on membership only),
`ExactLevelOrderSupplierShape`, `ExactLevelOrderSupplierExact`, and
`ExactLevelOrderStageCallback`:
`Emits levelOrder B high → HighAtStage f B high (stageChildren levelOrder B)`.

## What is assumed

`SelectedWithThreshold f B` for exactness and the stage contract; the emission equation for the
stage contract.

## What is not claimed

- No raw program. `levelOrder` is typed and `noncomputable`.
- No statement about order or multiplicity relative to `canonical`; the two lists are different
  lists with the same members. `stageChildren levelOrder B` and `stageChildren canonical B` are
  therefore different ordered lists, and only the former is intended for `Emits`.
- No new semantic content: exactness is transferred from #1394/#1395.
