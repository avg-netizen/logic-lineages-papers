# UNIFORM-NEAR-CLOSED-BLOCK — source map (Opus B, round 2, Part 1)

Targets: `LogicLineages/PermittedControl/UniformNearClosedBlockTargets.lean`, sha256
`0473f56ede0e82f751ef6795ed71b1782f6c3cc08566b559f5236c1c7820fac3`, frozen 2026-11-23T01:31Z after compiling alone (receipt
`1795397439900681705-3232524`).

Serves root's Part 1 and `CORRESPONDENCE-REVIEW.md` §4: joint computability of the near-control closed-block
decider in `b` and the encoded query.

## Program
`nearDecide (b,x) := OriginalPrintedRawStageQuery.result (nearControl b) (b+1) (highCode nearRendering) x`, with
`nearRendering := renderingWith guardCode`. This is the same rendering as the closed-block decision (#1418).

## Statements
- `ParametricSolveEffectivity`: the raw driver `solve` is jointly computable when the control and the bound
  program depend computably on a parameter. It is the #1340 effectivity redone with a parameter.
- `NearDecideComputable`: `Computable nearDecide`.
- `NearDecideExact`: `∀ b, Decides (nearControl b) (fun x => nearDecide (b,x))`.
- `UniformNearClosedBlockDecision`: the existential form root asked for.

## Route
The per-control effectivity chain is re-proved with a parameter. Each per-`f` lemma `Computable f → Computable (X f)`
becomes `Computable₂ F → Computable (fun x => X (F x.1) x.2)`, with the same constructions. The chain is:
1. encoded descent step and states, terminal scan test, bounded index, scan, search;
2. entry scan program, fixed-entry closed scan;
3. closed ordinary value and count fields;
4. field read and named read;
5. coordinate slice;
6. raw low clause, family and strips;
7. raw driver `lowCode`, `nextCode`, `advance`, `solve`;
8. conditional and stage query `result`.

Joint inputs: `Primrec₂ nearControl` (EffectivityTargets) and `Primrec₂ stageBound` (#1336).

Semantics per `b`: `ForControl (nearControl b) (b+1)` (#1372), the level-order supplier and emission (#1411–#1415), and the
guard rendering (#1418).
