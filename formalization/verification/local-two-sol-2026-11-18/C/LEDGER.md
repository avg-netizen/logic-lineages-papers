# Lane C ledger (root; papers 17, 18, 20)

## 2026-11-18 19:50–20:00 UTC — Paper17 unchanged-control hardness chain authored (unverified drafts)

Target statement: `cor:standard-functional-hardness` (17 hardness.tex 244–265).
The printed proof says the selected-control constructions apply literally with
f = G. The existing selected-control proofs take `SelectedWithThreshold ctrl K`,
which Phi does not satisfy, so each layer is rebuilt at Phi on the checked
standard-control suppliers. Nothing below is accepted until native gate,
axiom audit, evidence and independent review are complete.

1. StandardSeededCompiler (comparator frozen by the previous coordinator,
   paper17/STANDARD-SEEDED-COMPILER-FREEZE.json, seven pins, pre-scope approved).
   New proof modules: StandardSeededCompilerActualProof (compiler induction on
   StandardPairCompiler algebra + StandardOmegaSeed.actualScaledPair; assignment
   success/positivity from StandardFunctionalDetector values),
   StandardSeededSolvabilityProof (seed substitution and shared family from the
   arbitrary-control public suppliers; embedding/projection helpers reconstructed;
   both directions of solvability), StandardSeededCompilerProof,
   StandardSeededCompilerStatementChecks.
2. StandardSeededSystem. New comparator StandardSeededSystemTargets = accepted
   SelectedSeededSystemTargets with ctrl := Phi and the selected hypothesis
   removed (six families). Pins: paper17/STANDARD-SEEDED-SYSTEM-FREEZE.json.
   Proofs: StandardSeededSystemAssemblyProof, ...QueriesProof, ...EmptyProof,
   ...StatementChecks.
3. StandardSingleQuery. Comparator StandardSingleQueryTargets (five families;
   three are control-free program/calibration facts). Proof + StatementChecks.
4. StandardFunctionalHardness. Comparator StandardFunctionalHardnessTargets =
   the eight-clause theorem at Phi for every policy (finite-query level two,
   single-query level three, weak and strict). Proof uses StandardFiniteQuery
   (accepted packet 379), StandardSingleQuery and the two arbitrary-control
   decision pullbacks. Gate: StandardFunctionalHardnessStatementChecks
   (968-module closure, 243 cached at authoring time).

Open before any acceptance: pins for packets 3–4, native gates, evidence,
independent review (not by root). StandardOmegaSeed's full gate is a supplier
and is still pending from the previous coordinator's handoff.

Paper18: WholeBlockProjector staged gates queued behind the cache warm.

## 2026-11-18 21:03 UTC — Paper17 Phi chain gated: READY-FOR-INDEPENDENT-REVIEW (not by root)

All five gates passed on first native attempt under the unchanged Mathlib
profile (2048/1536/2048, one thread, CPU 90/wall 180), no source repair:
receipts 1795035731192527497-2023148 (seeded compiler) and
1795035739998193767-2023495 (Omega seed full alias, seeded system, single
query, functional hardness). Recursive compiler-free evidence, zero errors,
each alias on propext, Classical.choice, Quot.sound only:

| Packet | Gate | Modules | Evidence |
|---|---|---|---|
| StandardOmegaSeed (inherited comparator, full alias) | StandardOmegaSeedStatementChecks | 612 | paper17/STANDARD-OMEGA-SEED-EVIDENCE.json |
| StandardSeededCompiler | StandardSeededCompilerStatementChecks | 691 | paper17/STANDARD-SEEDED-COMPILER-EVIDENCE.json |
| StandardSeededSystem | StandardSeededSystemStatementChecks | 792 | paper17/STANDARD-SEEDED-SYSTEM-EVIDENCE.json |
| StandardSingleQuery | StandardSingleQueryStatementChecks | 813 | paper17/STANDARD-SINGLE-QUERY-EVIDENCE.json |
| StandardFunctionalHardness = cor:standard-functional-hardness | StandardFunctionalHardnessStatementChecks | 968 | paper17/STANDARD-FUNCTIONAL-HARDNESS-EVIDENCE.json |

Pins: STANDARD-OMEGA-SEED-FREEZE, STANDARD-SEEDED-COMPILER-FREEZE (inherited),
STANDARD-SEEDED-SYSTEM-FREEZE, STANDARD-SINGLE-QUERY-FREEZE,
STANDARD-FUNCTIONAL-HARDNESS-FREEZE. Scope: STANDARD-FUNCTIONAL-HARDNESS-SOURCE-MAP.md.
Root authored these, so root does not accept them; the independent review is
assigned to lane B at its next return. Register unchanged until then.
