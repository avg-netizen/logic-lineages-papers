# Checked original path checker

Date: 7 November 2026, America/Chicago.

All six frozen exact supporting targets passed on their first compiler runs.
The nine new source modules define a concrete original Program AST for ordinary
and positive path checking, calibrate it to the unchanged source checker on
every natural input, and prove its nil/cons acceptance equations inside the
original `InternalCalculus.Derivation`.

| Exact target | Checked conclusion |
| --- | --- |
| `ActualOriginalPathCheckerEvaluation` | The concrete ordinary checker equals the one/zero value of the literal original `pathTest` on the original decoded path. |
| `ActualOriginalPositivePathCheckerEvaluation` | The concrete positive checker equals the one/zero value of the literal original `positivePathTest`. |
| `ActualInternalPathNil` | Ordinary acceptance of nil is equivalent to equality of the source and target. |
| `ActualInternalPositivePathNil` | The positive checker rejects nil. |
| `ActualInternalPathCons` | Ordinary cons acceptance is equivalent to actual edge acceptance and ordinary tail acceptance. |
| `ActualInternalPositivePathCons` | Positive cons acceptance has the same edge-and-tail equation. |

The two evaluation targets use the explicit all-input calibration of the
supplied edge Program to the unchanged `numericEdgeTest`. The four internal
targets hold for every edge Program, with no calibration or Boolean-output
premise. Acceptance always means that its actual graph has output one.

## Concrete traversal and proof

`summary edge` invokes the checked original raw-list recursor. It keeps the
target vertex as a parameter, stores zero for nil, and stores a single original
cons cell for every nonempty suffix. That cell contains the suffix's first
raw pair-coded entry and the acceptance value obtained by running the tail
summary from the entry's next vertex.

`finish edge positive` reads the source, target and summary. On zero it compares
endpoints for an ordinary path and returns zero for a positive path. On a cons
summary it applies exact-one conjunction to the actual edge checker and the
stored suffix result. Its components are the original equality, conditional,
head, tail, unpair and normalization Program ASTs.

The internal proof first identifies the literal pair fields and summary-cell
fields through the original graph equations. `finishConsAccept` and
`finishConsRecover` relate acceptance to edge acceptance and the stored result
being equal to one. `summaryConsValue` obtains the actual summary graph from
the checked raw recursor constructor rule. `consEquation` chooses its summary,
suffix-result and cons-output witnesses using original Program totality and
eliminates them through the original existential rule. Graph functionality
identifies the suffix result with ordinary tail acceptance.

This argument does not infer derivability from standard-model evaluation. The
external calibration proves a separate fold invariant, then compares it with
the original `pathTest` recursion and total original path decoder.

## Contextual interfaces

`InternalPathCheckerProof` exports these rules for arbitrary `Gamma`:

- `pathNil edge x y`: the ordinary nil/equality equivalence.
- `positiveNil edge x y`: positive nil rejection.
- `pathCons edge x y code raw tail vertex certificate hp hc`: ordinary cons
  equivalence, where `hp` is the actual pairing graph of the raw entry and
  `hc` is the actual original cons graph.
- `positiveCons edge x y code raw tail vertex certificate hp hc`: the
  corresponding positive cons equivalence.

The public predicates are `InternalPathChecker.pathGraph edge x y code`,
`positiveGraph edge x y code` and `edgeGraph edge x vertex certificate`.
Both cons rules conclude acceptance equivalent to
`edgeGraph edge x vertex certificate` conjoined with
`pathGraph edge vertex y tail`. All positive calculus bodies, symbolic codes,
object-language terms and assumption contexts remain arbitrary.

The exact theorem aliases are `actualOriginalPathCheckerEvaluation` and
`actualOriginalPositivePathCheckerEvaluation` in `InternalPathCheckerEvaluationProof`,
and `actualInternalPathNil`, `actualInternalPositivePathNil`,
`actualInternalPathCons` and `actualInternalPositivePathCons` in
`InternalPathCheckerProof`.

## Acceptance

The final focused check used pinned Lean `v4.32.0-rc1`, one serialized worker,
a 2048 MiB heap cap, a 1536 MiB process-tree RSS cap and the unchanged 2048 MiB
free-memory floor. Peak observed process-tree RSS was 1,229,944 KiB.
Every exact alias reports only `[propext, Classical.choice, Quot.sound]`.

The frozen definition and target files are byte-for-byte unchanged.
`FINAL-CHECK.json` and `FINAL-CHECK.log` preserve the successful six-alias gate;
`ACCEPTED-MODULES.json` records successful source-matched checks for all nine
new modules, and `CHECKED-SOURCES.sha256` pins their accepted sources.
The root coordinator owns the larger aggregate dependency-closure check.

## Source scope

The checker operates on the unchanged numeric list of pairs of next vertices
and original edge certificates. These six supporting results supply the
internal traversal equations required for application-certificate lifting in
paper06 `lem:id1`. The downstream lifting argument still needs the local
internal application-edge preservation rule and the relevant domain invariant.
Source-specific multiset, constructor, lambda and all-term conclusions are not
asserted here. No numbered source statement or register entry is promoted.
