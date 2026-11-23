# Opus B ledger, round 4 (22 Nov)

Task (Root): (1) conditional `thm:upper` (prefix `ConditionalUpper`) from #489, #1460, R1, E4 with the
body-operator stage bridge proved; (2) conditional Paper 16 `thm:main` (prefix `ConditionalMain16`).
Rules: gate via `round4/gate.sh`; no git, no rm; round-2/3 files frozen; new twins via
`opusB/twin/make_twins.py` (round-4 copy, skips round-2 and round-3 twins after hash check) into
`opusB/twin/TWIN-MANIFEST-ROUND4.json`.

- Waiting for Opus A's `ExternalOrdinalInterfaceTargets.lean` before freezing ConditionalUpper targets.
- Bridge found (no new mathematics): `NumberedWindowConcreteFormulaChecks.exact_ConcretePresentation` (programs
  with `Evaluates` + `Interprets`) and `NumberedWindowOriginalPresentationChecks.exact_ActualOperatorAndTerms`
  (`tagged (checks S.entries (fixed S K)) P z ↔ taggedStep S K P z`) give pointwise equality of the syntactic
  body's operator with `taggedStep`, hence equal stages.
- Task 2 prep: 289 new twins for the item 1–5 closures (ProtectedSpineDecisionSplitChecks, StablePairChecks, NativeOrientationChecks, RankedRestrictionChecks; closure 533, 244 earlier twins skipped); 1 body change (one-word `private` on `ProtectedSpineSoundSourceProof.ExprValid`, used in public theorem `checkHeads`).
- Item 1–5 twins GATE PASSED: receipt `1795403782728682601-3286725` (533 modules, 289 compiled), peak RSS 339,556 KiB; `exact_Decidability`, `exact_fullStablePair` [propext, Classical.choice, Quot.sound], `exact_ExactRankedRestriction` [propext, Quot.sound]; `exact_fullOrientation` twin from round 2 (cache hit).
- Opus A interface read: `ExternalOrdinalInterfaceTargets` (sha e040bcb1…eb81; `UpperBound BH`) and
  `ExternalOrdinalInterfaceID1Targets` (sha 8e6ed85d…3c1c3b; E4 `NormTheorem BH`, R1 `InternalAccessibility d c`).
  E4 used verbatim. R1 not consumable as is (uniform all-terms sentence; the atom at tr(s)'s address needs internal
  ∀-elim + Σ₁-truth of the checker graph + a closed-term identity, none available as lemmas): own R1 in the
  printed individual form `ConditionalUpperTargets.IndividualAccessibility`.
- Bridge `ConditionalUpperBridgeTargets` (frozen sha 4e5091d2…ecb7, receipt `1795404030499321327-3289116`,
  1,018,140 KiB) / `ConditionalUpperBridgeProof.exact_BodyStageBridge` PASSED: receipt
  `1795404040274907395-3289223`, 1,046,436 KiB, [propext, Classical.choice, Quot.sound]. (108 new twins for
  `NumberedWindowOriginalPresentationChecks`'s closure.)
- `ConditionalUpperTargets` frozen (sha e43ba411d5e9b8d5ca367d26d6898c6807e69107cb37d92e616eb45bff8022e9, receipt
  `1795404249474493402-3290592`, 1,052,804 KiB). `ConditionalUpperProof.exact_ConditionalUpper : ConditionalUpper`
  PASSED first try: receipt `1795404272996421094-3290722`, 1,432 modules, peak 1,098,124 KiB at the proof module;
  [propext, Classical.choice, Quot.sound]; no sorryAx. Hypotheses: E4 `NormTheorem BH`, R1 `IndividualAccessibility`.
  Fixed-type-vs-whole-universe rank equality not needed (symbolic side is the full confined relation; norm side
  is the address side).
- Opus A's `ConditionalHeightTargets` (sha 35cd1d59…4274) / `ConditionalHeightProof.conditionalHeight` already
  gated (receipt `1795404261857473158-3290689`, rc 0) — imported directly, not taken as a hypothesis.
- `ConditionalMain16Targets` frozen (sha 53387e55f0f6f3c9efe5138b80eee5ca7aecbd937e8a62f1f6a32b07cfa2998f, receipt
  `1795404360683896399-3291086`, 1,049,648 KiB). `ConditionalMain16Proof.exact_ConditionalMain16` and
  `exact_Items1to5` PASSED first try: receipt `1795404377834098432-3291123`, 1,878 modules, peak 1,138,232 KiB at the
  proof module; [propext, Classical.choice, Quot.sound]; no sorryAx.
- Source maps `MAIN16-SOURCE-MAP.md`, `UPPER-SOURCE-MAP.md`; scopes `SCOPES.md`. Items 1–5: no mismatch; item 6c
  ("effective family") is not captured by `HeightIsBH`.
- Manifests re-hashed: round 2 671/0, round 3 43/0, round 4 397 twins (1 body change)/0 mismatches.
