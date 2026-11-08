# Checked original raw-list recursion and map

Date: 8 November 2026.

All six frozen exact supporting targets passed. The fourteen source modules
define a concrete primitive-recursive list recursor and its map specialization,
calibrate their evaluations on every natural input, and prove the literal nil
and cons graph equations inside the original `InternalCalculus.Derivation`.

| Component | Evaluation target | Internal graph targets |
| --- | --- | --- |
| `InternalRawListRecursion.listRec` | The right fold of the original decoded numeric list, with arbitrary base, step and parameter programs. | Nil is the base graph; original cons unfolds to an existential tail-result witness together with the original step graph. |
| `InternalListMap.map` | The original encoder applied to the mapped original decoded list, with arbitrary transform and parameters. | Nil maps to zero; cons maps to the literal original constructor applied to actual head-transform and tail-map graph witnesses. |

The constructor assumptions are the unchanged original cons graph. The results
retain all symbolic codes, free parameters, outputs and arbitrary positive
calculus bodies. Reusable supporting lemmas retain arbitrary hypothesis
contexts. No successful-decoding assumption restricts the evaluation targets.

## Internal argument

The concrete AST computes a finite table of results in increasing numeric code
order. The table uses the original list codec and stores the newest entry first.
At code `i+1`, the original head and tail programs produce the list constructor
arguments; the original subtraction and repeated-tail programs retrieve the
tail result from the previous table.

`InternalRawListRecursionTableProof.tableDrop` proves internally that dropping
`gap` entries from the table at `code+gap` yields the table at `code`.
`allRows` proves the universally quantified invariant by PA induction on the
gap. `tableLookup` combines it with the literal head graph. The original
`consTailDescent` theorem supplies the strict inequality required to express
a cons code as the successor of its tail code plus a difference witness.
`consAtGap` then assembles the actual next-value AST graph and
`consValue` transports the result back to the caller's symbolic code.

The evaluation proofs use a separate external invariant: the table at index
`i` contains the decoded-list fold for every code at most `i`. They do not
supply a reflection rule or substitute standard-model truth for a derivation.

## Reusable exact interfaces

The exact theorems are:

- `InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation`.
- `InternalRawListRecursionProof.actualOriginalListRecursionZero`.
- `InternalRawListRecursionProof.actualOriginalListRecursionCons`.
- `InternalListMapEvaluationProof.actualRawListMapEvaluation`.
- `InternalListMapProof.actualOriginalListMapZero`.
- `InternalListMapProof.actualOriginalListMapCons`.

The raw proof also exposes contextual `nilValue`, `nilRecover`, `consValue`,
`consForward`, `consBackward`, `stepIntroduction` and `stepCases` rules.

## Acceptance and preserved statements

The final focused coordinator passed under pinned Lean `v4.32.0-rc1` with one
worker, a 2048 MiB heap cap, a 1536 MiB process-tree RSS cap and the unchanged
2048 MiB free-memory floor. The final run observed peak process-tree RSS
1,224,568 KiB; the matching accepted checks for the fourteen new modules
observed at most 1,224,612 KiB. All six exact aliases report only
`[propext, Classical.choice, Quot.sound]`.

The four frozen definition/target files are byte-for-byte unchanged. Proof
repairs supplied explicit projection arguments, resolved one namespace alias
and selected the matching successor-substitution lemma. No target was
weakened and no resource limit was increased.

`FINAL-CHECK.json` and `FINAL-CHECK.log` retain the successful final gate.
`ACCEPTED-MODULES.json` records a matching successful check for every new source;
`CHECKED-SOURCES.sha256` pins those fourteen source files. The initial frozen
texts and hashes remain intact. Routine failed syntax logs remain in ignored
build reports. The root coordinator owns the larger dependency-closure gate.

## Source scope

This supplies original list traversal for paper06 `lem:id1` certificate lifting
and multiset arguments. The path-map specialization can combine this map AST
with concrete vertex and edge programs to realize the existing `liftPath`.
The internal preservation of positive path acceptance still requires original
checker equations and the relevant internal edge-preservation derivation.
The remaining source-specific closure arguments and the all-term accessibility
endpoint remain pending. No numbered source statement or register entry is
promoted by these six supporting targets.
